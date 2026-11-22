import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SigmaDefectEvalPhaseOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteTorsOfFiniteTorsion
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0030
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivIntegral
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeGermIntegral

variable {K : Type} [Field K]

def intRing (V : VF K) : Subring K where
  carrier := {a | V.Ge 0 a}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem intS_iff (V : VF K) {σ : Type} (f : MvPowerSeries σ K) :
    IntS V f ↔ f ∈ Ig (intRing V) K σ := by
  constructor
  · intro h
    exact ig_of_intAA fun n => ⟨⟨_, h n⟩, rfl⟩
  · intro h n
    obtain ⟨r, hr⟩ := intAA_of_ig h n
    rw [← hr]
    exact r.2

theorem map_self {σ : Type} (f : MvPowerSeries σ K) :
    MvPowerSeries.map (algebraMap K K) f = f := by
  ext n
  simp [coeff_map]

variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

omit [CharZero K] in
theorem FK_self (B : FB K d O) : B.FK K = B.G.F := funext fun _ => map_self _

open GlobalTheory.GaugeSecondDeriv in

theorem second_deriv (B : FB K d O) (h : PS K 2 d) (hc : B.IsCanonGauge K h) (b : Fin d) :
    ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) -
        ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b) B.ph2) := by
  have hA : ∀ c, constantCoeff (addOf B.G.F (pt K (n := 3) d 1) (pt K d 2) c) = 0 :=
    fun c => constantCoeff_ev LogPf.cz12 (B.G.const c)
  have c02 : CZ (![pt K (n := 3) d 0, pt K d 2] : Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
      Fin 2 → Pt K 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt K d 0, pt K d 1] h +
      ev (n := 3) ![pt K d 0, pt K d 2] h -
      ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hE := hc.ph2
  rw [FB.toK, map_self, FK_self] at hE
  have hH := pderiv_expS hH0 ((2 : Fin 3), b)
  rw [← hE] at hH
  have t1 : pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt K d 0, pt K d 1, 0]
      (pderiv K ((2 : Fin 3), b) (ev (n := 3) ![pt K d 0, pt K d 2] h)) =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b)
      (ev (n := 3) ![pt K d 0, addOf B.G.F (pt K d 1) (pt K d 2)] h)) =
      ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt K d 0, pt K d 1, 0]
        ((![pt K (n := 3) d 0, addOf B.G.F (pt K (n := 3) d 1) (pt K d 2)] :
          Fin 2 → Pt K 3 d) i c)) = fun i => pt K (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis B.G c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.G.F j) b
  rw [hH, ev_mul czZ, B.cocycleRight_zero_thd, one_mul, map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3]
  ring

variable {V : VF K}

theorem ev_sgP (Y : FBChart K V O d) (v : Fin d → K) {n : ℕ} (a : Pt K n d)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    ev ![a] (Y.sgP v) = ∑ i, C (v i) * ev ![a] (sgOf K Y.h i) := by
  have h1 : CZ (![a] : Fin 1 → Pt K n d) := CZ.cons ha CZ.nil
  rw [FBChart.sgP, ev_neg h1, ev_sum h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : sgOf K Y.h i = -ev (n := 1) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), i) Y.h) := rfl
  rw [ev_mul h1, ev_C h1, e, ev_neg h1, mul_neg]

omit [CharZero K] in
theorem int_comb (v : Fin d → K) (hv : ∀ i, V.Ge 0 (v i)) (f : PS K 3 d) (hf : IntS V f) :
    (∑ i, C (v i) * ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), i) f)) ∈
      Ig (intRing V) K (Fin 2 × Fin d) :=
  sum_mem fun i _ => mul_mem (ig_C (R := intRing V) ⟨v i, hv i⟩)
    (ig_ev czZ integral_family_pair_zero (ig_pderiv ((intS_iff V f).1 hf) _))

theorem cocycle_integral (Y : FBChart K V O d) : GermISt Y := by
  intro v hv
  have hadd : addOf Y.B.G.F (pt K (n := 2) d 0) (pt K d 1) = Y.B.G.F := by
    funext i
    have e : (![pt K (n := 2) d 0, pt K d 1] : Fin 2 → Pt K 2 d) = fun j => pt K d j := by
      funext j
      fin_cases j <;> rfl
    rw [addOf, e, ev_pt]
  rw [intS_iff, hadd, ev_sgP Y v _ Y.B.G.const, ev_sgP Y v _ (cc_pt 0), ev_sgP Y v _ (cc_pt 1),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  convert int_comb v hv _ Y.intPh1 using 2 with i
  have e := GlobalTheory.SigmaDefect.sgOf_defect Y.B Y.h Y.gauge i
  rw [FB.toK, map_self, FK_self] at e
  rw [e]
  ring

theorem invariant_deriv_integral (Y : FBChart K V O d) : GermIISt Y := by
  intro v hv
  rw [intS_iff, ev_sgP Y v _ (cc_pt 0)]
  convert neg_mem (int_comb v hv _ Y.intPh2) using 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := second_deriv Y.B Y.h Y.gauge i
  rw [GlobalTheory.SigmaDefect.ev_sgOf _ _ _ (cc_pt 0)]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, e]
  ring

theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), GermISt Y ∧ GermIISt Y :=
  fun _ _ _ _ _ _ _ _ Y => ⟨cocycle_integral Y, invariant_deriv_integral Y⟩

end GlobalTheory.GaugeGermIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsAddUnitOfPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharExt

private theorem isAddUnit_of_pow {M : Type} [AddCommMonoid M] {p : ℕ} (hp : p ≠ 0) {a : M}
    (h : ∃ k, p ^ k • a = 0) : IsAddUnit a := by
  obtain ⟨k, hk⟩ := h
  have h1 : p ^ k = (p ^ k - 1) + 1 := by
    have : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ hp)
    omega
  rw [h1, add_nsmul, one_nsmul, add_comm] at hk
  exact ⟨⟨a, (p ^ k - 1) • a, hk, by rw [add_comm]; exact hk⟩, rfl⟩

private theorem extend_group {A B : Type} [AddCommGroup A] [AddCommGroup B] (j : A →+ B)
    (hj : Function.Injective j) (C : Type) [Field C] [IsAlgClosed C]
    (χ : A →+ Additive Cˣ) : ∃ κ : B →+ Additive Cˣ, ∀ a, κ (j a) = χ a := by
  classical
  have hsurj : ∀ n : ℕ, n ≠ 0 → ∀ x : Additive Cˣ, ∃ y : Additive Cˣ, n • y = x := by
    intro n hn x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : Cˣ) : C)
      (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact (Additive.toMul x : Cˣ).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    ext
    simpa using hz
  letI : DivisibleBy (Additive Cˣ) ℕ :=
    divisibleByOfSMulRightSurj (Additive Cˣ) ℕ (fun {n} hn x => hsurj n hn x)
  letI : DivisibleBy (Additive Cˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨κ, hκ⟩ := (Module.Baer.of_divisible (Additive Cˣ)).extension_property_addMonoidHom
    j hj χ
  exact ⟨κ, fun a => DFunLike.congr_fun hκ a⟩

theorem exists_extension : ∀ (M M' : Type) [AddCommMonoid M] [AddCommMonoid M'] (j : M' →+ M), Function.Injective j → ∀ (C : Type) [Field C] [IsAlgClosed C] (p : ℕ), p ≠ 0 → ∀ χ : M' → Cˣ, (∀ a b, χ (a + b) = χ a * χ b) → ∃ κ : M → Cˣ, (∀ a b, (∃ k, p ^ k • a = 0) → (∃ k, p ^ k • b = 0) → κ (a + b) = κ a * κ b) ∧ κ 0 = 1 ∧ ∀ a, (∃ k, p ^ k • a = 0) → κ (j a) = χ a := by
  intro M M' _ _ j hj C _ _ p hp χ hχ
  classical
  let χ' : AddUnits M' →+ Additive Cˣ := AddMonoidHom.mk' (fun u => Additive.ofMul (χ u.val))
    (fun a b => by rw [AddUnits.val_add, hχ]; rfl)
  have hj' : Function.Injective (AddUnits.map j) := by
    intro a b hab
    ext
    exact hj (congrArg AddUnits.val hab)
  obtain ⟨κ, hκ⟩ := extend_group (AddUnits.map j) hj' C χ'
  have key : ∀ u : AddUnits M,
      (if h : IsAddUnit u.val then Additive.toMul (κ h.addUnit) else 1) = Additive.toMul (κ u) := by
    intro u
    rw [dif_pos u.isAddUnit]
    congr 2
    ext
    exact IsAddUnit.addUnit_spec _
  refine ⟨fun a => if h : IsAddUnit a then Additive.toMul (κ h.addUnit) else 1, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    obtain ⟨v, rfl⟩ := isAddUnit_of_pow hp hb
    have h3 := key (u + v)
    have h1 := key u
    have h2 := key v
    beta_reduce
    rw [h1, h2]
    refine Eq.trans h3 ?_
    rw [map_add]; rfl
  · have := key 0
    refine Eq.trans this ?_
    rw [map_zero]; rfl
  · intro a ha
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    have h1 := key (AddUnits.map j u)
    refine Eq.trans h1 ?_
    rw [hκ]; rfl

end GlobalTheory.CharExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem nv_eq_sum {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) (N : ℕ) (hN : ∀ q : Fin n × Fin d, a q.1 q.2 ^ N = 0) :
    nv s f a = ∑ e : Fin n × Fin d → Fin N, s (MvPowerSeries.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f) * ∏ i, a i.1 i.2 ^ (e i : ℕ) := by
  letI := s.toAlgebra
  exact evBasic_nEval_eq_tEval f (fun q : Fin n × Fin d => a q.1 q.2) N hN

private theorem nEval_sqZero {R S κ : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype κ] [DecidableEq κ]
    (f : MvPowerSeries κ R) (a : κ → S) (ha : ∀ i, IsNilpotent (a i)) (h : ∀ i j, a i * a j = 0) :
    nEval f a = algebraMap R S (MvPowerSeries.constantCoeff f) +
      ∑ q, algebraMap R S (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q := by
  have h0 : ∀ i : κ, IsNilpotent ((0 : κ → S) i) := fun _ => IsNilpotent.zero
  have hm : ∀ i, a i ∈ Ideal.span (Set.range a) := fun i => Ideal.subset_span ⟨i, rfl⟩
  have h1 := ChartCompare.nEval_sub_mem f a 0 ha h0 _ _ hm (fun _ => Ideal.zero_mem _)
    (fun i => by simpa using hm i)
  have h2 : Ideal.span (Set.range a) * Ideal.span (Set.range a) ≤ ⊥ := by
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact h i j
  have h3 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal S))
    (evBasic_nEval_sub_coeff_mem f (0 : κ → S) h0)
  have h4 := h2 h1
  rw [Ideal.mem_bot, sub_eq_zero] at h3 h4
  rw [h3, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_eq_iff_eq_add'] at h4
  simpa [Algebra.smul_def] using h4

theorem nv_calculus : ∀ (R S : Type) [CommRing R] [CommRing S] (s : R →+* S) (n d : ℕ) (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) → (∃ ψ : PS R n d →+* S, (∀ f, ψ f = nv s f a) ∧ (∀ c, ψ (MvPowerSeries.C c) = s c) ∧ ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) ∧ (∀ f : PS R n d, MvPowerSeries.constantCoeff f = 0 → IsNilpotent (nv s f a) ∧ nv s f a ∈ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) ∧ (∀ (m e : ℕ) (b : Fin m → Fin e → PS R n d) (f : PS R m e), (∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) → nv s (sub b f) a = nv s f (fun i j => nv s (b i j) a)) ∧ (∀ (R' : Type) [CommRing R'] (β : R' →+* R) (f : PS R' n d), nv (s.comp β) f a = nv s (MvPowerSeries.map β f) a) ∧ (∀ (S' : Type) [CommRing S'] (t : S →+* S') (f : PS R n d), t (nv s f a) = nv (t.comp s) f (fun i j => t (a i j))) ∧ ((∀ i j i' j', a i j * a i' j' = 0) → ∀ f : PS R n d, nv s f a = s (MvPowerSeries.constantCoeff f) + ∑ q : Fin n × Fin d, s (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q.1 q.2) := by
  intro R S _ _ s n d a ha
  have ha' : ∀ q : Fin n × Fin d, IsNilpotent (a q.1 q.2) := fun q => ha _ _
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow (fun q : Fin n × Fin d => a q.1 q.2) ha'
  letI := s.toAlgebra
  refine ⟨?_, fun f hf => ⟨ChartCompare.isNilpotent_nEval f hf _ ha', ?_⟩, fun m e b f hb => ?_,
    fun R' _ β f => ?_, fun S' _ t f => ?_,
    fun h f => nEval_sqZero f (fun q : Fin n × Fin d => a q.1 q.2) ha' fun _ _ => h _ _ _ _⟩
  · let ψ : PS R n d →+* S := (MvPowerSeries.constantCoeff : MvPowerSeries Empty S →+* S).comp
      (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).toRingHom
    have hψ : ∀ f, ψ f = nv s f a := fun f => by
      simp [ψ, nv, MvPowerSeries.coe_substAlgHom, ChartCompare.subst_C_eq f _ ha']
    refine ⟨ψ, hψ, fun c => ?_, fun q => (hψ _).trans (ChartCompare.nEval_X _ ha' q)⟩
    have := (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).commutes c
    exact (congrArg MvPowerSeries.constantCoeff this).trans (by
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C]; rfl)
  · have := evBasic_nEval_sub_coeff_mem f _ ha'
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero, sub_zero] at this
    exact this
  · exact ChartCompare.nEval_subst (fun q : Fin m × Fin e => b q.1 q.2) (fun q => hb _ _) f _ ha'
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ a N hN]
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ _ N (fun q => by rw [← map_pow, hN q, map_zero])]
    simp only [map_sum, map_mul, map_prod, map_pow, RingHom.comp_apply]

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNMap
section
set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in

theorem nabValN_map : ∀ (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] (ψ : S →+* S') (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (B' : FB S' d O), (∀ i, B'.G.F i = MvPowerSeries.map ψ (B.G.F i)) → (∀ a i, B'.A.act a i = MvPowerSeries.map ψ (B.A.act a i)) → ∀ (h : PS S 2 d), MvPowerSeries.constantCoeff h = 0 → ∀ (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S), nabValN B' S' (MvPowerSeries.map ψ h) w0 m (MvPowerSeries.map ψ f) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) = ψ (nabValN B S h w0 m f cp u P) := by
  intro S S' _ _ _ _ ψ d O _ _ B B' hF hA h hc w0 m n f κ _ cp u P
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B'.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S' S') (B'.G.F i)
    rw [hF]
    ext e
    simp [coeff_map]
  have eA : mapP ψ (B.actK S w0) = B'.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S' S') (B'.A.act w0 i)
    rw [hA]
    ext e
    simp [coeff_map]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B'.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B'.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEq
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def lowZero {A κ : Type} [CommRing A] (e : κ →₀ ℕ) : Ideal (MvPowerSeries κ A) where
  carrier := {g | ∀ e' ≤ e, MvPowerSeries.coeff e' g = 0}
  add_mem' {a b} ha hb e' h := by rw [map_add, ha e' h, hb e' h, add_zero]
  zero_mem' e' _ := map_zero _
  smul_mem' c x hx e' h := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2 (le_trans (le_of_le_of_eq le_add_self (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)) h), mul_zero]

private theorem coeff_box {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (N : ℕ) (c : (κ →₀ ℕ) → A)
    (e : κ →₀ ℕ) (he : ∀ i, e i < N) :
    MvPowerSeries.coeff e (∑ b : κ → Fin N, MvPowerSeries.C (c (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
      ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ (b i : ℕ)) = c e := by
  have hm : ∀ b : κ → ℕ, ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ b i =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm b) 1 := fun b => by
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have he' : (Finsupp.equivFunOnFinite.symm fun i => ((⟨e i, he i⟩ : Fin N) : ℕ)) = e := by
    ext i; rfl
  rw [map_sum, Finset.sum_eq_single (fun i => (⟨e i, he i⟩ : Fin N))]
  · rw [hm, MvPowerSeries.coeff_C_mul, he', MvPowerSeries.coeff_monomial_same, _root_.mul_one]
  · intro b _ hb
    rw [hm, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial_ne, mul_zero]
    intro h
    exact hb (funext fun i => Fin.ext (by simp [h]))
  · simp

theorem eq_of_nv_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  intro R _ I hI n d f f' H
  ext e
  rw [← sub_eq_zero]
  refine hI.haus _ fun k => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  let A := R ⧸ I ^ (k + 1)
  let J : Ideal (MvPowerSeries (Fin n × Fin d) A) := lowZero e
  let N : ℕ := (∑ i, e i) + 1
  have he : ∀ i, e i < N := fun i =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have halg : ∀ t : R, algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J) t =
      Ideal.Quotient.mk J (MvPowerSeries.C (Ideal.Quotient.mk (I ^ (k + 1)) t)) := fun t => by
    rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply]; rfl
  have hN : ∀ q : Fin n × Fin d, (Ideal.Quotient.mk J (MvPowerSeries.X q)) ^ N = 0 := fun q => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    intro e' h
    exact (MvPowerSeries.X_pow_dvd_iff.1 dvd_rfl) e' (lt_of_le_of_lt (h q) (he q))
  have hv : ∀ g : PS R n d, nv (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)) g
      (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) =
      Ideal.Quotient.mk J (∑ b : Fin n × Fin d → Fin N, MvPowerSeries.C ((fun x => Ideal.Quotient.mk (I ^ (k + 1))
        (MvPowerSeries.coeff x g)) (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
        ∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n × Fin d) A) ^ (b i : ℕ)) := fun g => by
    letI := (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)).toAlgebra
    refine (evBasic_nEval_eq_tEval g (fun q : Fin n × Fin d => Ideal.Quotient.mk J (MvPowerSeries.X q)) N hN).trans ?_
    simp only [tEval, map_sum, map_mul, map_prod, map_pow]
    exact Finset.sum_congr rfl fun b _ => congrArg (· * _) (halg _)
  have h := H (MvPowerSeries (Fin n × Fin d) A ⧸ J) k (fun t ht => by
      rw [halg, Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero, map_zero]) (fun hR hne => ?_)
    (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) (fun i j => ⟨N, hN (i, j)⟩)
  · rw [hv, hv, Ideal.Quotient.eq] at h
    have h2 := h e le_rfl
    rw [map_sub, sub_eq_zero] at h2
    exact Ideal.Quotient.eq.1 (((coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f)) e he).symm.trans h2).trans (coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f')) e he))
  · have hA : I ^ (k + 1) ≠ ⊤ := fun h => hne (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero k)))
    haveI : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 hA
    haveI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hJ : J ≠ ⊤ := fun h => by
      have : (1 : MvPowerSeries (Fin n × Fin d) A) ∈ J := h ▸ Submodule.mem_top
      have := this 0 zero_le
      simp at this
    haveI : Nontrivial (MvPowerSeries (Fin n × Fin d) A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
    refine ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, ⟨fun t ht => ?_⟩⟩
    rw [halg] at ht
    have h1 := (IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).map_nonunit _ ht
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h1
    exact (IsLocalHom.of_surjective (Ideal.Quotient.mk (I ^ (k + 1))) Ideal.Quotient.mk_surjective).map_nonunit _ h1

end GlobalTheory.ChF
end
end

