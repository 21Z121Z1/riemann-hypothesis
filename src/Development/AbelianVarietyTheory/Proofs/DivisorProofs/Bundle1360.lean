import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZ
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

def lineSubst {K : Type} [Field K] {N : ℕ} (a b : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K →ₐ[K] Polynomial K :=
  aeval fun p : Fin 1 × Fin N => Polynomial.C (a p.2) + Polynomial.C (b p.2) * Polynomial.X

theorem line_eq_lineSubst {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (a b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    line s a b f = lineSubst a b (spec s f) := by
  simp only [line, spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, lineSubst]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K),
      IsScalarTower.algebraMap_apply F K (Polynomial K), AlgHom.commutes]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join, lineSubst]

theorem eval_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) = aeval (join s b) f := by
  simp only [spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K)]
    simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join]

theorem lineSubst_lin {K : Type} [Field K] {N : ℕ} (a b y : Fin N → K) :
    lineSubst a b (lin y) = Polynomial.C (∑ j, a j * y j) + Polynomial.C (∑ j, b j * y j) * Polynomial.X := by
  simp only [lin, lineSubst, map_sum, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_eq, add_mul,
    Finset.sum_add_distrib, Polynomial.C_mul, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eval_lin {K : Type} [Field K] {N : ℕ} (b y : Fin N → K) :
    eval (fun p : Fin 1 × Fin N => b p.2) (lin y) = ∑ j, b j * y j := by
  simp [lin]

theorem coeff_ne_zero_of_resultant_ne_zero {K : Type} [Field K] {δ : ℕ} (hδ : 1 ≤ δ) (P : Polynomial K)
    (hP : P.natDegree ≤ δ) (h : Polynomial.resultant P (Polynomial.derivative P) δ (δ - 1) ≠ 0) : P.coeff δ ≠ 0 := by
  by_contra hc
  apply h
  have hlt : P.natDegree < δ := by
    rcases hP.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero] at h1
      omega
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [Polynomial.leadingCoeff, h1]; exact hc))
  rcases Nat.lt_or_ge δ 2 with h2 | h2
  · obtain rfl : δ = 1 := by omega
    have hd : Polynomial.derivative P = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0), Polynomial.derivative_C]
    simp [hd]
  · apply Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _ hlt
    calc (Polynomial.derivative P).natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
      _ < δ - 1 := by omega

theorem noSquare_spec_of_disc_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  intro F K _ _ _ D N δ f s a b hδ hdeg hcoeff hdisc
  have hres : (line s a b f).resultant (Polynomial.derivative (line s a b f)) δ (δ - 1) ≠ 0 := hdisc
  have hc : (line s a b f).coeff δ ≠ 0 := coeff_ne_zero_of_resultant_ne_zero hδ _ hdeg hres
  have hspec0 : eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) ≠ 0 := by
    rw [eval_spec, ← hcoeff]
    exact hc
  refine ⟨fun h0 => hspec0 (by rw [h0, map_zero]), fun y _ hdvd => ?_⟩
  obtain ⟨q, hq⟩ := hdvd
  by_cases hβ : ∑ j, b j * y j = 0
  · apply hspec0
    rw [hq, map_mul, map_pow, eval_lin, hβ]
    simp
  · have hnat : (line s a b f).natDegree = δ :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc
    have hP0 : line s a b f ≠ 0 := fun h0 => hc (by rw [h0, Polynomial.coeff_zero])
    have hcop : IsCoprime (line s a b f) (Polynomial.derivative (line s a b f)) := by
      by_contra hnc
      apply hres
      have hd' : (Polynomial.derivative (line s a b f)).natDegree ≤ δ - 1 := by
        rw [← hnat]
        exact Polynomial.natDegree_derivative_le _
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd'
      rw [hk, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, ← hnat,
        Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hP0, hnc⟩, mul_zero]
    have hQ : line s a b f = lineSubst a b (lin y) * lineSubst a b (lin y) * lineSubst a b q := by
      rw [line_eq_lineSubst, hq, map_mul, map_pow, sq]
    have h1 : lineSubst a b (lin y) ∣ line s a b f :=
      ⟨lineSubst a b (lin y) * lineSubst a b q, by rw [hQ]; ring⟩
    have h2 : lineSubst a b (lin y) ∣ Polynomial.derivative (line s a b f) := by
      refine ⟨Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        lineSubst a b (lin y) * Polynomial.derivative (lineSubst a b q), ?_⟩
      rw [hQ, Polynomial.derivative_mul, Polynomial.derivative_mul]
      ring
    have hu := hcop.isUnit_of_dvd' h1 h2
    rw [lineSubst_lin] at hu
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [add_comm, Polynomial.natDegree_linear hβ] at hdeg0
    exact one_ne_zero hdeg0

end GlobalTheory.PencilDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralRestrictedProductEqProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RestrProd

theorem twOrb_restrProd : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  intro ι G _ _ _ H _ _ _ _ p K KH δ f hpc hinj hglue hfin hK hcpt hKc hcomm hloc hstab hsupp hgood
  have hT : ∀ x, x ∈ twCent (MonoidHom.id G) δ ↔ ∀ i, p i x ∈ twCent (MonoidHom.id (H i)) (p i δ) := by
    intro x
    simp only [GlobalTheory.TwOrbConj.mem_twCent, MonoidHom.id_apply]
    constructor
    · intro h i
      rw [← map_mul, h, map_mul]
    · intro h
      apply hinj
      intro i
      rw [map_mul, h i, map_mul]
  have hC := GlobalTheory.T.mem_compactPart_centralizer_iff_local ι G H p KH _ _ hpc hfin hcpt hKc hT hcomm
  have hCT : ∀ i, cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ twCent (MonoidHom.id (H i)) (p i δ) :=
    fun i => (Subgroup.closure_le _).2 (fun t ht => ht.1)
  have havg1 : ∀ (M : Type) [Group M], avg (fun _ : M => (1 : ℂ)) = 1 := by
    intro M _
    have hR : rStab (fun _ : M => (1 : ℂ)) = ⊤ := by
      ext k
      simp [GlobalTheory.TwOrbConj.mem_rStab]
    unfold avg
    rw [hR, Subgroup.index_top]
    haveI : Subsingleton (M ⧸ (⊤ : Subgroup M)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (M ⧸ (⊤ : Subgroup M)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
    simp [finsum_unique]
  have hs : ∀ g, GlobalTheory.TwOrbConj.summand (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) g =
      ∏ᶠ i, GlobalTheory.TwOrbConj.summand (MonoidHom.id (H i)) (KH i) (p i δ) (f i) (p i g) := by
    intro g
    have hrel := GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct ι G H p K _ _ KH _ _ g hglue hfin hK hT hC hCT (fun i => hloc i (p i g))
      (hgood.mono fun i h => h.2.2.2)
    have hu1 : ∀ᶠ i in cofinite, ∀ k : KH i, f i ((p i g * k)⁻¹ * p i δ * (p i g * k)) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg k
      rw [h.2.1]
      apply Set.indicator_of_mem
      exact (KH i).mul_mem ((KH i).mul_mem ((KH i).inv_mem ((KH i).mul_mem hg k.2)) h.1) ((KH i).mul_mem hg k.2)
    have havg := GlobalTheory.T.groupAverage_componentwiseSubgroup_eq_prod ι G H p K KH hK (fun i k => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) hglue
      (fun i => hstab i (p i g)) hu1
    have hr1 : ∀ᶠ i in cofinite, (((twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) : ℕ) : ℂ) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg
      rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2), Nat.cast_one]
    have ha1 : ∀ᶠ i in cofinite, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = 1 := by
      filter_upwards [hu1] with i h
      rw [show (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = fun _ => 1 from funext h]
      exact havg1 _
    have e1 : avg (fun k : K => ∏ᶠ i, f i (p i ((g * ↑k)⁻¹ * δ * (MonoidHom.id G) (g * ↑k)))) =
        ∏ᶠ i, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) := by
      rw [← havg]
      congr 1
      funext k
      simp [map_mul, map_inv]
    unfold GlobalTheory.TwOrbConj.summand
    simp only [MonoidHom.id_apply] at e1 ⊢
    have hN : Function.HasFiniteMulSupport fun i => (twCent (MonoidHom.id (H i)) (p i δ) ⊓
        (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) := by
      have : ∀ᶠ i in cofinite, (twCent (MonoidHom.id (H i)) (p i δ) ⊓
          (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) = 1 := by
        filter_upwards [hgood, hfin g] with i h hg
        rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2)]
      exact Filter.eventually_cofinite.1 this
    have hcast := map_finprod (Nat.castRingHom ℂ) hN
    simp only [eq_natCast] at hcast
    rw [e1, hrel, hcast, ← finprod_mul_distrib (Filter.eventually_cofinite.1 hr1) (Filter.eventually_cofinite.1 ha1)]
  rw [GlobalTheory.TwOrbConj.twOrb_eq]
  simp only [GlobalTheory.TwOrbConj.twOrb_eq]
  refine GlobalTheory.T.finsum_doubleCoset_eq_finprod_local_sums ι G H p _ K _ KH _ _ hglue hfin hK hT ?_ ?_ ?_ hs
  · intro i t ht k hk x
    exact GlobalTheory.TwOrbConj.summand_rep _ _ _ _ x ht hk
  · intro i
    refine (hsupp i).subset ?_
    intro q hq
    by_contra hcon
    apply hq
    have h0 : (fun k : KH i => f i ((Quotient.out q * k)⁻¹ * p i δ * (MonoidHom.id (H i)) (Quotient.out q * k))) =
        fun _ => 0 := by
      funext k
      by_contra hk
      exact hcon ⟨k, k.2, hk⟩
    unfold GlobalTheory.TwOrbConj.summand
    rw [h0]
    simp [avg]
  · filter_upwards [hgood] with i h x
    rw [h.2.1]
    exact GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator (H i) (KH i) (p i δ) h.1 h.2.2.2 h.2.2.1 x

end GlobalTheory.RestrProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClass
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.OrbUnit
open DoubleCoset

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have h1 : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [h1, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := ⟨⟨QuotientGroup.mk 1⟩, fun a => Subsingleton.elim _ _⟩
  rw [finsum_unique]
  simp

theorem twOrb_unit {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G)
    (horb : ∀ g₁ g₂ : G, g₁⁻¹ * γ * g₁ ∈ K → g₂⁻¹ * γ * g₂ ∈ K →
      ∃ t ∈ twCent (MonoidHom.id G) γ, ∃ k ∈ K, g₂ = t * g₁ * k)
    (hcpt : ∀ g : G, g⁻¹ * γ * g ∈ K →
      cptPart (twCent (MonoidHom.id G) γ) ≤ K.map (MulAut.conj g).toMonoidHom) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = if ∃ g : G, g⁻¹ * γ * g ∈ K then 1 else 0 := by
  classical
  set T := twCent (MonoidHom.id G) γ with hT
  have hTle : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hterm : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      ((((T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart T) : ℕ) : ℂ) *
        avg fun k : K => (K : Set G).indicator 1 ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
      = if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
    intro q
    have hconst : (fun k : K => (K : Set G).indicator (1 : G → ℂ)
        ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
        = fun _ => if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
      funext k
      have he : (Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)
          = (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k := by
        simp only [MonoidHom.id_apply]; group
      rw [he]
      by_cases hm : (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) k.2
        simp [Set.indicator_of_mem this, hm]
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∉ K := by
          intro h; apply hm
          have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem k.2)
          simpa [mul_assoc] using this
        simp [Set.indicator_of_notMem this, hm]
    rw [hconst, avg_const]
    split_ifs with hm
    · rw [(Subgroup.relIndex_eq_one).2 (le_inf hTle (hcpt _ hm))]; simp
    · simp
  rw [twOrb, finsum_congr hterm]
  split_ifs with hex
  · obtain ⟨g₀, hg₀⟩ := hex
    have hgood : ∀ g : G, g ∈ doubleCoset g₀ (T : Set G) (K : Set G) → g⁻¹ * γ * g ∈ K := by
      intro g hg
      obtain ⟨t, ht, k, hk, rfl⟩ := mem_doubleCoset.1 hg
      have htc : t * γ = γ * t := by simpa [hT, twCent] using ht
      have : (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * γ * g₀) * k := by
        have : t⁻¹ * γ * t = γ := by rw [mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]
        calc (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * (t⁻¹ * γ * t) * g₀) * k := by group
          _ = _ := by rw [this]
      rw [this]; exact K.mul_mem (K.mul_mem (K.inv_mem hk) hg₀) hk
    rw [finsum_eq_single _ (DoubleCoset.mk T K g₀)]
    · rw [if_pos]
      obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul T K g₀
      apply hgood
      rw [he]; exact mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩
    · intro q hq
      rw [if_neg]
      intro hm
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := horb g₀ (Quotient.out q) hg₀ hm
      rw [← DoubleCoset.out_eq' T K q, DoubleCoset.eq]
      exact ⟨t⁻¹, T.inv_mem ht, k⁻¹, K.inv_mem hk, by rw [he]; group⟩
  · push_neg at hex
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro q; rw [if_neg (hex _)]

end GlobalTheory.BCT.OrbUnit

namespace GlobalTheory.BCT.OrbUnit

theorem orbUnit_ae : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ γ : UL n w, γ.1.val.charpoly = atPl w P → (twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = if ∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w then 1 else 0) ∧ kapSign n w (atPl w P) γ.1 = 1 ∧ ∀ Q₁ : (w.adicCompletion E)[X], Q₁ ∣ atPl w P → (∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) → kapSign n w Q₁ γ.1 = 1 := by
  intro E _ _ _ _ n _ S _ P hP
  filter_upwards [GlobalTheory.T.eventually_integral_lift_coprime_derivative E P hP.2.2.1] with w hw
  obtain ⟨P₀, hmap, hcop⟩ := hw
  obtain ⟨hσσ, hv⟩ := GlobalTheory.T.localConjugation_involutive_valuation_preserving E w
  intro γ hγ
  have hγ' : γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [hγ, hmap]
  refine ⟨?_, ?_, ?_⟩
  · exact twOrb_unit (KL n w) γ (GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w hσσ hv P₀ hcop γ hγ') (GlobalTheory.T.compactPart_centralizer_le_conj_integralUnitary E n w P₀ hcop γ hγ')
  · rw [← hγ]; exact GlobalTheory.T.localSign_full_charpoly_eq_one E n w hv γ.1
  · rintro Q₁ hQ ⟨g, hg⟩
    rw [← GlobalTheory.T.localSign_kernel_charFactor_conj_invariant E n w hv Q₁ γ g]
    refine GlobalTheory.T.unitaryLocalSign_eq_one_of_integral_separable_reduction E n w hσσ hv P₀ hcop (g⁻¹ * γ * g) ?_ hg Q₁ (by rw [hmap]; exact hQ)
    rw [← hγ']
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val =
        ((g : GLw n w)⁻¹ : GLw n w).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [this, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end GlobalTheory.BCT.OrbUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermIntegralExpression
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

noncomputable def centEquiv (G : HTGroup p) (P : Pair G) (hpos : ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ))
    (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    Subgroup.centralizer ({r} : Set (grp G P.β)) ≃* P.cent where
  toFun y := ⟨y.1.1, by
    have h := congrArg (fun a : grp G P.β => (a : G.Cˣ × ℚˣ).1)
      (Subgroup.mem_centralizer_singleton_iff.1 y.2)
    simp only [Subgroup.coe_mul, hr, Prod.fst_mul] at h
    exact h, y.1.2.1⟩
  invFun y := ⟨⟨y.1, y.2.2, hpos y.1 y.2⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hr]
    exact Prod.ext y.2.1 (mul_comm _ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fix_iff_mark (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (P : Pair G) (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) ↔ ∃ μ, P.Mark μ := by
  have hV : (toV G v P.β r : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (P.γ : G.C) := by
    show G.psi v (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = _
    rw [hr]
  constructor
  · rintro ⟨z, hz, c, hc⟩
    rw [hV] at hc
    exact ⟨c, v, hv, z, hc, hz⟩
  · rintro ⟨μ, w, hw, z, hz, hpos⟩
    have h1 : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := hG.le
    have hvv : w = v := congrArg Subtype.val (Fintype.card_le_one_iff.1 h1 ⟨w, hw⟩ ⟨v, hv⟩)
    subst hvv
    exact ⟨z, hpos, μ, by rw [hV]; exact hz⟩

end GlobalTheory.LKCx.Regroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvectorStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_archimedean_eigenvector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  first | exact @GlobalTheory.LineGlue.exists_idele_smul_of_local_lines | exact GlobalTheory.LineGlue.exists_idele_smul_of_local_lines | (intros; apply GlobalTheory.LineGlue.exists_idele_smul_of_local_lines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeff
section
set_option autoImplicit false

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

theorem prod_pow_natDegree_le_and_coeff {R ι : Type} [CommRing R] (s : Finset ι) (v : ι → Polynomial R) (w m : ι → ℕ)
    (h : ∀ p, (v p).natDegree ≤ w p) :
    (∏ p ∈ s, v p ^ m p).natDegree ≤ ∑ p ∈ s, m p * w p ∧
      (∏ p ∈ s, v p ^ m p).coeff (∑ p ∈ s, m p * w p) = ∏ p ∈ s, (v p).coeff (w p) ^ m p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have h1 : (v p ^ m p).natDegree ≤ m p * w p :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (h p))
    rw [Finset.prod_insert hp, Finset.sum_insert hp, Finset.prod_insert hp]
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add h1 ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih.1, ih.2,
      Polynomial.coeff_pow_of_natDegree_le (h p)]

theorem line_natDegree_le_and_coeff (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (u : Fin D → Fin N → R) (a b : Fin N → R) :
    (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧
      (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  classical
  set v : Fin (D + 1) × Fin N → Polynomial R :=
    join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X with hv
  let w : Fin (D + 1) × Fin N → ℕ := fun p => if p.1 = Fin.last D then 1 else 0
  have hdeg : ∀ p, (v p).natDegree ≤ w p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hv, w, join, if_true, Fin.lastCases_last]
      rw [add_comm]
      exact Polynomial.natDegree_linear_le
    · simp [hv, w, join]
  have hco : ∀ p, (v p).coeff (w p) = join u b p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [hv, w, join]
    · simp [hv, w, join]
  have hsum : ∀ m ∈ f.support, ∑ p, m p * w p = δ := by
    intro m hm
    have := hf m (by simpa using hm) (Fin.last D)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa [w] using this
    · intro i _ hi
      simp [w, hi]
    · simp
  have hkey : ∀ m ∈ f.support, (∏ p, v p ^ m p).natDegree ≤ δ ∧
      (∏ p, v p ^ m p).coeff δ = ∏ p, join u b p ^ m p := by
    intro m hm
    have := prod_pow_natDegree_le_and_coeff Finset.univ v w m hdeg
    rw [hsum m hm] at this
    simpa only [hco] using this
  have hline : line u a b f =
      ∑ m ∈ f.support, Polynomial.C (algebraMap F R (f.coeff m)) * ∏ p, v p ^ m p := by
    rw [line, ← hv, aeval_def, eval₂_eq']
    rfl
  rw [hline, aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hkey m hm).1, ?_⟩
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Polynomial.coeff_C_mul, (hkey m hm).2]

end GlobalTheory.PencilDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFieldsStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields : ∀ (F σ τ : Type) [Field F] [Finite σ] [Finite τ] (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F)), (∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0) → ∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω), (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  first | exact @GlobalTheory.PointTransfer.solvable_transfer | exact GlobalTheory.PointTransfer.solvable_transfer | (intros; apply GlobalTheory.PointTransfer.solvable_transfer <;> assumption)
end

