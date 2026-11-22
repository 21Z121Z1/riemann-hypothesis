import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0009
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Ring

variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)

theorem jetCoef_mk (κ : Type) (m : ℕ) (p : MvPolynomial κ V) :
    jetCoef f κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

theorem psTrunc_map {σ : Type} [Fintype σ] [DecidableEq σ] (m : ℕ) (F : MvPowerSeries σ V) :
    psTrunc m (MvPowerSeries.map f F) = MvPolynomial.map f (psTrunc m F) := by
  simp only [psTrunc, map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem jetCoef_alg (κ : Type) (m : ℕ) :
    (jetCoef f κ m).comp (algebraMap V (Jet V κ m)) = (algebraMap K (Jet K κ m)).comp f := by
  refine RingHom.ext fun v => ?_
  first
  | (show jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
     rw [jetCoef_mk, MvPolynomial.map_C])
  | (simp only [RingHom.comp_apply]
     rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
       MvPolynomial.algebraMap_eq, jetCoef_mk, MvPolynomial.map_C])

theorem jetCoef_aug (κ : Type) (m : ℕ) :
    ((jetAug : Jet K κ m →ₐ[K] K) : Jet K κ m →+* K).comp (jetCoef f κ m) =
      f.comp ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C a))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.C a)))
    rw [jetCoef_mk, MvPolynomial.map_C]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.C (f a)) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.C a))
    simp
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    rw [jetCoef_mk, MvPolynomial.map_X]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.X i) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.X i))
    simp

theorem jetCoef_trunc (κ : Type) (m : ℕ) :
    ((jetTrunc : Jet K κ (m + 1) →ₐ[K] Jet K κ m) : Jet K κ (m + 1) →+* Jet K κ m).comp (jetCoef f κ (m + 1)) =
      (jetCoef f κ m).comp ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  first
  | rfl
  | simp [jetCoef_mk, jetTrunc]

theorem jetCoef_map {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ')
    (hφ' : ∀ i, MvPolynomial.map f (φ i) ∈ orig K κ') :
    (jetCoef f κ' m).comp ((jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetMap (fun i => MvPolynomial.map f (φ i)) hφ' : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.C a))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.C a)))
    rw [jetCoef_mk]
    simp
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.X i))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.X i)))
    rw [jetCoef_mk]
    simp

end Ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
section
set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem expActOf_of (hE : LinEigSt) : ExpActOfSt := expActOf_of_eig hE

end Formalism.MainNotions.ModuliIntegralCharts.H1
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJetA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

variable {R : Type} [CommRing R]

theorem ker_fst_sq : RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ (0 + 1 + 1) = ⊥ := by
  show RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ 2 = ⊥
  rw [sq, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx' : x.fst = 0 := by simpa using hx
  have hy' : y.fst = 0 := by simpa using hy
  rw [Ideal.mem_bot]
  ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx', hy']

def tp {κ : Type} (g : κ → R) : Jet R κ (0 + 1) →ₐ[R] DualNumber R :=
  liftJet (MvPolynomial.aeval fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (by
    apply le_bot_iff.1
    refine (Ideal.pow_right_mono (Ideal.span_le.2 ?_) _).trans (le_of_eq ker_fst_sq)
    rintro _ ⟨q, rfl⟩
    simp)

theorem tp_mk {κ : Type} (g : κ → R) (q : κ) :
    tp g (Ideal.Quotient.mk _ (MvPolynomial.X q)) = TrivSqZeroExt.inr (g q) := by
  show MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]

theorem zero_ne_single {κ : Type} (q : κ) : (0 : κ →₀ ℕ) ≠ Finsupp.single q 1 :=
  (Finsupp.single_ne_zero.mpr one_ne_zero).symm

theorem aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (P : MvPolynomial κ R) :
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) P =
      TrivSqZeroExt.inl (MvPolynomial.coeff 0 P) +
        TrivSqZeroExt.inr (∑ q, g q * MvPolynomial.coeff (Finsupp.single q 1) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.coeff_C, zero_ne_single, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add, hp, hq]
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib, TrivSqZeroExt.inl_add,
      TrivSqZeroExt.inr_add]
    abel
  | mul_X p n hp =>
    have hc : ∀ q, MvPolynomial.coeff (Finsupp.single q 1) (p * MvPolynomial.X n) =
        if q = n then MvPolynomial.coeff 0 p else 0 := by
      intro q
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : q = n
      · subst h
        simp
      · rw [if_neg h, if_neg]
        rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]
        exact fun h' => h h'.symm
    have h0 : MvPolynomial.coeff 0 (p * MvPolynomial.X n) = 0 := by
      rw [MvPolynomial.coeff_mul_X']
      simp
    rw [map_mul, hp, MvPolynomial.aeval_X, h0]
    ext <;> simp [hc, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, mul_comm]

private lemma coeff_psTrunc_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R)
    (e : κ →₀ ℕ) (he : e.degree < 0 + 1 + 1) :
    MvPolynomial.coeff e (psTrunc (0 + 1) f) = MvPowerSeries.coeff e f := by
  rw [psTrunc_eq, MvPowerSeries.coeff_truncTotal _ he]

theorem tp_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (f : MvPowerSeries κ R) :
    tp g (psJet (0 + 1) f) = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff f) +
      TrivSqZeroExt.inr (∑ q, g q * MvPowerSeries.coeff (Finsupp.single q 1) f) := by
  have h1 : tp g (psJet (0 + 1) f) =
      MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (psTrunc (0 + 1) f) := rfl
  rw [h1, aeval_inr, coeff_psTrunc_lemma f 0 (by simp [Finsupp.degree]),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeff_psTrunc_lemma f _ (by simp [Finsupp.degree_single])]

theorem jetTan_eq_tp {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) = tp (fun q => if q = ℓ then 1 else 0) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0)
      (MvPolynomial.X i) =
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (if q = ℓ then 1 else 0) : DualNumber R))
      (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  by_cases h : i = ℓ
  · (simp only [if_pos h]) <;> rfl
  · simp only [if_neg h, TrivSqZeroExt.inr_zero]

theorem tp_comp_jetMap {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (h : κ' → R) (a : κ → MvPowerSeries κ' R)
    (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) :
    (tp h).comp (jetMap (m := 0 + 1) (fun p => psTrunc (0 + 1) (a p)) (fun p => psTrunc_mem_orig (0 + 1) (a p) (ha p))) =
      tp (fun p => ∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  have h1 : (jetMap (m := 0 + 1) (fun p => psTrunc (0 + 1) (a p))
      (fun p => psTrunc_mem_orig (0 + 1) (a p) (ha p))) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
        psJet (0 + 1) (a p) := by
    show (Ideal.Quotient.mk (orig R κ' ^ (0 + 1 + 1)))
      (MvPolynomial.aeval (fun p => psTrunc (0 + 1) (a p)) (MvPolynomial.X p)) = _
    rw [MvPolynomial.aeval_X] <;> rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, tp_psJet, ha p, tp_mk]
  simp

theorem snd_tp_psJet_subst {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (h : κ' → R)
    (a : κ → MvPowerSeries κ' R) (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) (f : MvPowerSeries κ R) :
    (tp h (psJet (0 + 1) (MvPowerSeries.subst a f))).snd =
      ∑ p, (∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) *
        MvPowerSeries.coeff (Finsupp.single p 1) f := by
  rw [psJet_subst (0 + 1) a ha f, ← AlgHom.comp_apply, tp_comp_jetMap h a ha, tp_psJet]
  simp

theorem sum_coeff_X {κ : Type} [Fintype κ] [DecidableEq κ] (h : κ → R) (s : κ) :
    ∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (MvPowerSeries.X s : MvPowerSeries κ R) = h s := by
  simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

theorem sum_coeff_variable_pair {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (h : κ₁ → κ₂ → R)
    (s : κ₁ × κ₂) :
    ∑ i, ∑ j, h i j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      h s.1 s.2 := by
  obtain ⟨s1, s2⟩ := s
  rw [Finset.sum_eq_single s1, Finset.sum_eq_single s2]
  · simp [MvPowerSeries.coeff_X]
  · intro j _ hj
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hj]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hi]
  · simp

theorem sum_coeff_X_fst {κ₁ κ₂ : Type} [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] (u : κ₂ → R) (i : κ₁)
    (s : κ₁ × κ₂) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      if i = s.1 then u s.2 else 0 := by
  obtain ⟨s1, s2⟩ := s
  dsimp only
  by_cases hi : i = s1
  · subst hi
    rw [if_pos rfl, Finset.sum_eq_single s2]
    · simp [MvPowerSeries.coeff_X]
    · intro j _ hj
      simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hj]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hi]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem lin_unit {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst (fun q : Fin 1 × Fin d => u q.2)
    (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) ha (G.F k)
  have hu : MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2)
      (G.F k) = MvPowerSeries.X ((0 : Fin 1), k) := G.unit k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 0 i) = 0 := by
    intro i
    simp
  have inner1 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 1 i) = u i :=
    fun i => sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), i)
  rw [hu, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, zero_mul, Finset.sum_const_zero, zero_add] at key
  rw [← key, tp_psJet]
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), k)

theorem lin_comm {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  set h : Fin 2 × Fin d → R := fun q => if q.1 = 0 then u q.2 else 0 with hh
  have h_0 : ∀ j, h ((0 : Fin 2), j) = u j := fun j => by simp [hh]
  have h_1 : ∀ j, h ((1 : Fin 2), j) = 0 := fun j => by simp [hh]
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst h
    (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) ha (G.F k)
  have hc : MvPowerSeries.subst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) (G.F k) = G.F k :=
    G.comm k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 0 i) = 0 :=
    fun i => (sum_coeff_X h ((1 : Fin 2), i)).trans (h_1 i)
  have inner1 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 1 i) = u i :=
    fun i => (sum_coeff_X h ((0 : Fin 2), i)).trans (h_0 i)
  rw [hc, tp_psJet] at key
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at key
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, h_0, h_1, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at key
  rw [key]
  exact lin_unit G u k

theorem lin_F {d : ℕ} (G : FGLaw R d) (v w : Fin d → R) (k : Fin d) :
    ∑ p : Fin 2 × Fin d, (![v, w] : Fin 2 → Fin d → R) p.1 p.2 *
      MvPowerSeries.coeff (Finsupp.single p 1) (G.F k) = v k + w k := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [lin_comm G v k, lin_unit G w k]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem split_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hIdef
  set p' : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hp'def
  have hmax : p'.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : p' ≠ ⊥ := by
    rw [hp'def, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p' = I := by
    rw [hp'def, Ideal.map_span, Set.image_singleton, map_natCast]
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := normalizedFactors I with hMdef

  have hmem : ∀ P : Ideal (𝓞 E), P ∈ M ↔ P.IsPrime ∧ I ≤ P := fun P => Ideal.mem_normalizedFactors_iff hI0
  have hne : ∀ P ∈ M, P ≠ ⊥ := fun P hP h0 => hI0 (eq_bot_iff.2 (h0 ▸ ((hmem P).1 hP).2))
  have hlies : ∀ P ∈ M, P.LiesOver p' := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
    have hle : p' ≤ P.under ℤ := by
      rw [hp'def, Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P
      rw [map_natCast]
      exact hIP (Ideal.subset_span rfl)
    have hnt : P.under ℤ ≠ ⊤ := by
      intro ht
      apply hPp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [ht]; trivial
      change algebraMap ℤ (𝓞 E) 1 ∈ P at h1
      rwa [map_one] at h1
    exact ⟨hmax.eq_of_le hnt hle⟩
  have hcard1 : M.toFinset.card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset]
    have himg : HeightOneSpectrum.asIdeal '' {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} =
        (M.toFinset : Set (Ideal (𝓞 E))) := by
      ext P
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine (hmem _).2 ⟨v.isPrime, ?_⟩
        rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]
        exact hv
      · intro hP
        obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
        exact ⟨⟨P, hPp, hne P hP⟩, hIP (Ideal.subset_span rfl), rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]
  haveI := hmax
  have hsum := Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0
  have hfs : IsDedekindDomain.primesOverFinset p' (𝓞 E) = M.toFinset := by
    rw [IsDedekindDomain.primesOverFinset, hmap, hMdef, factors_eq_normalizedFactors]
  have hle : ∑ P ∈ M.toFinset, M.count P ≤ Module.finrank ℚ E := by
    rw [← hsum, hfs]
    refine Finset.sum_le_sum fun P hP => ?_
    have hPM : P ∈ M := Multiset.mem_toFinset.1 hP
    haveI := hlies P hPM
    haveI : P.IsPrime := ((hmem P).1 hPM).1
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (by rw [hmap]; exact hI0) ‹P.IsPrime› (hne P hPM), hmap]
    exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg'_pos p' P)
  have hcard : M.card = ∑ P ∈ M.toFinset, M.count P := (Multiset.toFinset_sum_count_eq M).symm
  have h1 : M.toFinset.card ≤ M.card := Multiset.toFinset_card_le M
  have hMc : M.card = Module.finrank ℚ E := le_antisymm (hcard ▸ hle) (hcard1 ▸ h1)
  exact ⟨hMc, Multiset.toFinset_card_eq_card_iff_nodup.1 (hcard1.trans hMc.symm)⟩

open Formalism.BasicNotions in

theorem g_splits (D : D7) (i : Fin 2) :
    (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧
      (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup :=
  split_of_ncard (D.host.g_prime i) (D.nd.g_split i)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {R : Type} [CommRing R]

theorem coeff_eq_of_psJet {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} {a b : MvPowerSeries ι R}
    (h : psJet D a = psJet D b) {e : ι →₀ ℕ} (he : e.degree ≤ D) :
    MvPowerSeries.coeff e a = MvPowerSeries.coeff e b := by
  have h' : Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D a) =
      Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D b) := h
  have hm := Ideal.Quotient.eq.mp h'
  have h0 := coeff_eq_zero_of_mem hm (show e.degree < D + 1 by omega)
  rw [MvPolynomial.coeff_sub, coeff_psTrunc D a e he, coeff_psTrunc D b e he] at h0
  exact sub_eq_zero.mp h0

theorem psJet_subst_congr {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (D : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f g : MvPowerSeries σ R}
    (h : psJet D f = psJet D g) : psJet D (MvPowerSeries.subst a f) = psJet D (MvPowerSeries.subst a g) := by
  rw [psJet_subst D a ha f, psJet_subst D a ha g, h]

def psJetM {ι : Type} [Fintype ι] [DecidableEq ι] (D : ℕ) : MvPowerSeries ι R →* Jet R ι D where
  toFun := psJet D
  map_one' := psJet_one D
  map_mul' := psJet_mul D

theorem psJet_prod_congr {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (D : ℕ)
    {f g : κ → MvPowerSeries ι R} (h : ∀ b, psJet D (f b) = psJet D (g b)) :
    psJet D (∏ b, f b) = psJet D (∏ b, g b) := by
  change psJetM D (∏ b, f b) = psJetM D (∏ b, g b)
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun b _ => h b

theorem cc_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {g : MvPowerSeries σ R}
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (MvPowerSeries.subst a g) = 0 := MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha hg

theorem subst_exp {σ τ : Type} [Finite σ] [Algebra ℚ R] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (g : MvPowerSeries σ R)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst a (PowerSeries.subst g (PowerSeries.exp R)) =
      PowerSeries.subst (MvPowerSeries.subst a g) (PowerSeries.exp R) := by
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hg

theorem prod_exp {τ : Type} [Algebra ℚ R] : ∀ (n : ℕ) (q : Fin n → MvPowerSeries τ R),
    (∀ b, MvPowerSeries.constantCoeff (q b) = 0) →
    ∏ b, PowerSeries.subst (q b) (PowerSeries.exp R) = PowerSeries.subst (∑ b, q b) (PowerSeries.exp R)
  | 0, q, _ => by rw [Fin.prod_univ_zero, Fin.sum_univ_zero, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  | n + 1, q, hq => by
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, prod_exp n (fun b => q b.succ) (fun b => hq _),
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (ha := hq 0)
        (hb := by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hq _)]

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
end
end

