import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationHomogeneous
section
set_option backward.isDefEq.respectTransparency false

open MvPolynomial

namespace GlobalTheory.CompanionTheory.ConeNoether

theorem prod_pow_lead {R ι : Type*} [CommRing R] (s : Finset ι) (e : ι → ℕ)
    (g : ι → Polynomial R) (c : ι → R) (hd : ∀ i, (g i).natDegree ≤ 1)
    (hc : ∀ i, (g i).coeff 1 = c i) :
    (∏ i ∈ s, g i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, g i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, c i ^ e i :=
  _root_.UpperTheory.Reformulated.B.Yra8.main s e g c hd hc

theorem isIntegral_of_homogeneous_relation {K R S ι : Type*} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S] [Fintype ι]
    (F : MvPolynomial ι K) {n : ℕ} (hF : F.IsHomogeneous n) (a : ι → K) (ha : eval a F ≠ 0)
    (v : ι → R) (u : S)
    (h0 : aeval (fun i => algebraMap R S (v i) + algebraMap K S (a i) * u) F = 0) :
    IsIntegral R u := by
  classical
  let g : ι → Polynomial R := fun i =>
    Polynomial.C (v i) + Polynomial.C (algebraMap K R (a i)) * Polynomial.X
  have hgd : ∀ i, (g i).natDegree ≤ 1 := fun i => by
    simpa [g, add_comm] using
      Polynomial.natDegree_linear_le (a := algebraMap K R (a i)) (b := v i)
  have hgc : ∀ i, (g i).coeff 1 = algebraMap K R (a i) := fun i => by
    simp [g, Polynomial.coeff_C]
  have hdeg : ∀ d ∈ F.support, ∑ i, d i = n := fun d hd => by
    have := hF (mem_support_iff.1 hd)
    simpa [Finsupp.degree_eq_sum, Finsupp.weight_apply, Finsupp.sum_fintype] using this
  let p : Polynomial R := aeval g F
  have hp : p = ∑ d ∈ F.support,
      Polynomial.C (algebraMap K R (coeff d F)) * ∏ i, g i ^ d i := by
    simp only [p, aeval_def, eval₂_eq']
    rfl
  have hpd : p.natDegree ≤ n := by
    rw [hp]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    have := (prod_pow_lead Finset.univ d g _ hgd hgc).1
    rwa [hdeg d hd] at this
  have hpc : p.coeff n = algebraMap K R (eval a F) := by
    rw [hp, eval_eq', map_sum, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun d hd => ?_
    have := (prod_pow_lead Finset.univ d g _ hgd hgc).2
    rw [hdeg d hd] at this
    rw [Polynomial.coeff_C_mul, this]
    simp
  have hpe : Polynomial.eval₂ (algebraMap R S) u p = 0 := by
    have h1 := comp_aeval_apply (R := K) (f := g)
      ((Polynomial.aeval (R := R) u).restrictScalars K) F
    have h2 : (fun i => ((Polynomial.aeval (R := R) u).restrictScalars K) (g i)) =
        fun i => algebraMap R S (v i) + algebraMap K S (a i) * u := by
      funext i
      simp [g, IsScalarTower.algebraMap_apply K R S]
    rw [h2, h0] at h1
    simpa [Polynomial.aeval_def, p] using h1
  let b : R := algebraMap K R (eval a F)⁻¹
  have hb : b * algebraMap K R (eval a F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  refine ⟨Polynomial.C b * p, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
      ((Polynomial.natDegree_C_mul_le _ _).trans hpd) ?_
    rw [Polynomial.coeff_C_mul, hpc, hb]
  · rw [Polynomial.eval₂_mul, hpe, mul_zero]

theorem homogeneousComponent_aeval {K σ ι : Type*} [Field K] (l : ι → MvPolynomial σ K)
    (hl : ∀ i, (l i).IsHomogeneous 1) (F : MvPolynomial ι K) (n : ℕ) :
    homogeneousComponent n (aeval l F) = aeval l (homogeneousComponent n F) := by
  classical
  have key : ∀ k, homogeneousComponent n (aeval l (homogeneousComponent k F)) =
      if n = k then aeval l (homogeneousComponent k F) else 0 := fun k => by
    have h := (homogeneousComponent_isHomogeneous k F).aeval l hl
    rw [one_mul] at h
    exact homogeneousComponent_of_mem h
  conv_lhs => rw [← sum_homogeneousComponent F]
  rw [map_sum, map_sum]
  simp only [key, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem exists_homogeneous_relation {K σ ι : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I) (l : ι → MvPolynomial σ K)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (h : ¬ AlgebraicIndependent K fun i => Ideal.Quotient.mk I (l i)) :
    ∃ (d : ℕ) (F : MvPolynomial ι K), F ≠ 0 ∧ F.IsHomogeneous d ∧ aeval l F ∈ I := by
  rw [algebraicIndependent_iff] at h
  push_neg at h
  obtain ⟨F, hF, hF0⟩ := h
  have hmem : aeval l F ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hF]
    have := comp_aeval_apply (R := K) (f := l) (Ideal.Quotient.mkₐ K I) F
    simpa using this
  obtain ⟨n, hn⟩ : ∃ n, homogeneousComponent n F ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hF0 (by rw [← sum_homogeneousComponent F]; simp [hc])
  exact ⟨n, _, hn, homogeneousComponent_isHomogeneous n F, by
    rw [← homogeneousComponent_aeval l hl]; exact hI _ hmem n⟩

theorem isIntegral_trans_subalgebra {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (A R : Subalgebra K S) (h : ∀ x ∈ A, IsIntegral R x) (s : S) (hs : IsIntegral A s) :
    IsIntegral R s := by
  let φ : A →+* integralClosure R S :=
    { toFun := fun x => ⟨x.1, h x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h1 : IsIntegral (integralClosure R S) s :=
    IsIntegral.map_of_comp_eq φ (RingHom.id S) (by ext; rfl) hs
  exact isIntegral_trans s h1

theorem exists_linear_of_integral {K σ : Type} [Field K] [Infinite K]
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I)
    (hne : I ≠ ⊤) (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] (l : ι → MvPolynomial σ K), Fintype.card ι = n →
      (∀ i, (l i).IsHomogeneous 1) →
      (∀ s : MvPolynomial σ K ⧸ I,
        IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i))) s) →
      ∃ (m : ℕ) (y : Fin m → MvPolynomial σ K), (∀ i, (y i).IsHomogeneous 1) ∧
        AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧
        ∀ s : MvPolynomial σ K ⧸ I,
          IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) s := by
  classical
  have hnt : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  have done : ∀ (ι : Type) [Fintype ι] (l : ι → MvPolynomial σ K),
      (∀ i, (l i).IsHomogeneous 1) →
      (∀ s : MvPolynomial σ K ⧸ I,
        IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i))) s) →
      AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (l i)) →
      ∃ (m : ℕ) (y : Fin m → MvPolynomial σ K), (∀ i, (y i).IsHomogeneous 1) ∧
        AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧
        ∀ s : MvPolynomial σ K ⧸ I,
          IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) s := by
    intro ι _ l hl hs hind
    let e := Fintype.equivFin ι
    refine ⟨_, fun i => l (e.symm i), fun i => hl _, hind.comp _ e.symm.injective, ?_⟩
    have hr : (Set.range fun i => Ideal.Quotient.mk I (l (e.symm i))) =
        Set.range fun i => Ideal.Quotient.mk I (l i) :=
      e.symm.surjective.range_comp fun i => Ideal.Quotient.mk I (l i)
    rw [hr]
    exact hs
  induction n with
  | zero =>
    intro ι _ l hc hl hs
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
    exact done ι l hl hs (algebraicIndependent_empty_type_iff.2 (algebraMap K _).injective)
  | succ n ih =>
    intro ι _ l hc hl hs
    by_cases hind : AlgebraicIndependent K fun i => Ideal.Quotient.mk I (l i)
    · exact done ι l hl hs hind
    obtain ⟨d, F, hF0, hFd, hFI⟩ := exists_homogeneous_relation I hI l hl hind
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨j⟩ := this
    have hGd : (X j * F).IsHomogeneous (1 + d) := (isHomogeneous_X K j).mul hFd
    have hG0 : (X j * F : MvPolynomial ι K) ≠ 0 := mul_ne_zero (X_ne_zero j) hF0
    obtain ⟨a, ha⟩ : ∃ a : ι → K, eval a (X j * F) ≠ 0 := by
      by_contra hc'
      push_neg at hc'
      exact hG0 (MvPolynomial.funext fun x => by simpa using hc' x)
    have haj : a j ≠ 0 := fun h0 => ha (by simp [h0])
    have hGI : aeval l (X j * F) ∈ I := by
      rw [map_mul]
      exact I.mul_mem_left _ hFI
    let u : MvPolynomial σ K := C (a j)⁻¹ * l j
    let v : ι → MvPolynomial σ K := fun i => l i - C (a i) * u
    have hvj : v j = 0 := by
      simp only [v, u]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ haj, C_1, one_mul, sub_self]
    have hvh : ∀ i, (v i).IsHomogeneous 1 := fun i =>
      (hl i).sub (((hl j).C_mul _).C_mul _)
    let R := Algebra.adjoin K (Set.range fun i : {i // i ≠ j} => Ideal.Quotient.mk I (v i.1))
    have hmem : ∀ i, Ideal.Quotient.mk I (v i) ∈ R := fun i => by
      by_cases h : i = j
      · subst h
        rw [hvj, map_zero]
        exact zero_mem _
      · exact Algebra.subset_adjoin ⟨⟨i, h⟩, rfl⟩
    have hdec : ∀ i, Ideal.Quotient.mk I (v i) +
        algebraMap K (MvPolynomial σ K ⧸ I) (a i) * Ideal.Quotient.mk I u =
        Ideal.Quotient.mk I (l i) := fun i => by
      have : algebraMap K (MvPolynomial σ K ⧸ I) (a i) = Ideal.Quotient.mk I (C (a i)) := rfl
      rw [this, ← map_mul, ← map_add]
      simp only [v, sub_add_cancel]
    have hu : IsIntegral R (Ideal.Quotient.mk I u) := by
      refine isIntegral_of_homogeneous_relation (X j * F) hGd a ha
        (fun i => (⟨_, hmem i⟩ : R)) _ ?_
      have h1 : (fun i => algebraMap R (MvPolynomial σ K ⧸ I) ⟨_, hmem i⟩ +
          algebraMap K (MvPolynomial σ K ⧸ I) (a i) * Ideal.Quotient.mk I u) =
          fun i => Ideal.Quotient.mkₐ K I (l i) := by
        funext i
        exact hdec i
      rw [h1, ← comp_aeval_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hGI
    have hA : ∀ x ∈ Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i)),
        IsIntegral R x := by
      have hle : Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i)) ≤
          (integralClosure R (MvPolynomial σ K ⧸ I)).restrictScalars K := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨i, rfl⟩
        change IsIntegral R _
        simp only []
        rw [← hdec i]
        refine IsIntegral.add ?_ (IsIntegral.mul ?_ hu)
        · exact isIntegral_algebraMap (x := (⟨_, hmem i⟩ : R))
        · rw [IsScalarTower.algebraMap_apply K R]
          exact isIntegral_algebraMap
      exact fun x hx => hle hx
    refine ih {i // i ≠ j} (fun i => v i.1) ?_ (fun i => hvh _) fun s =>
      isIntegral_trans_subalgebra _ R hA s (hs s)
    simp [Fintype.card_subtype_compl, hc]

theorem main : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)), I ≠ ⊤ →
    (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) →
    ∃ (e m : ℕ) (y : Fin m → MvPolynomial (Fin (N + 1)) K), 0 < e ∧
      (∀ i, (y i).IsHomogeneous e) ∧
      AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧
      Module.Finite (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i)))
        (MvPolynomial (Fin (N + 1)) K ⧸ I) := by
  intro K _ _ N I hne hI
  have htop : ∀ s : MvPolynomial (Fin (N + 1)) K ⧸ I,
      s ∈ Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (X i)) := by
    intro s
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    induction f using MvPolynomial.induction_on with
    | C a => exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  obtain ⟨m, y, hy, hind, hint⟩ := exists_linear_of_integral I hI hne _ (Fin (N + 1)) X rfl
    (fun i => isHomogeneous_X K i)
    (fun s => isIntegral_algebraMap (x := (⟨s, htop s⟩ :
      Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (X i)))))
  refine ⟨1, m, y, one_pos, hy, hind, ?_⟩
  have : Algebra.IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i)))
      (MvPolynomial (Fin (N + 1)) K ⧸ I) := ⟨hint⟩
  have : Algebra.FiniteType K (MvPolynomial (Fin (N + 1)) K ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ_surjective K I)
  have : Algebra.FiniteType (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i)))
      (MvPolynomial (Fin (N + 1)) K ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  exact Algebra.IsIntegral.finite

end GlobalTheory.CompanionTheory.ConeNoether
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullCOfInvM
section
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell.NullCompl

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G]

theorem rp_mk_inv (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (P := P) (((g⁻¹ : G)) : G ⧸ P) = p * g := by
  refine ⟨(Quotient.out ((g⁻¹ : G) : G ⧸ P))⁻¹ * g⁻¹, ?_, ?_⟩
  · exact QuotientGroup.eq.mp (QuotientGroup.out_eq' ((g⁻¹ : G) : G ⧸ P))
  · simp [rp]

theorem rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  refine ⟨(Quotient.out (x⁻¹ • q))⁻¹ * (x⁻¹ * Quotient.out q), ?_, ?_⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe,
      QuotientGroup.out_eq']
  · simp [rp, mul_assoc]

variable [TopologicalSpace G]

theorem isOpen_rp [IsTopologicalGroup G] (P : Subgroup G) {Ω : Set G} (hΩ : IsOpen Ω)
    (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) : IsOpen {q : G ⧸ P | rp q ∈ Ω} := by
  have hset : {q : G ⧸ P | rp q ∈ Ω} = ((↑) : G → G ⧸ P) '' {g | g⁻¹ ∈ Ω} := by
    ext q
    constructor
    · intro hq
      refine ⟨(rp q)⁻¹, by simpa using hq, ?_⟩
      simp only [rp, inv_inv]
      exact QuotientGroup.out_eq' q
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨p, hp, hrp⟩ := rp_mk_inv P g⁻¹
      simp only [inv_inv] at hrp
      show rp (g : G ⧸ P) ∈ Ω
      rw [hrp]
      exact hP p hp _ hg
  rw [hset]
  exact QuotientGroup.isOpenMap_coe _ (hΩ.preimage continuous_inv)

theorem ratio_bound {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [IsTopologicalGroup G]
    (hS : Setup P h mu) {V : Set G} (hV : IsCompact V) :
    ∃ B : ℝ, ∀ g, ∀ x ∈ V, h (g * x) / h g ≤ B := by
  obtain ⟨C, hC, hcov⟩ := hS.cocpt
  have hcont : Continuous (fun z : G × G => h (z.1 * z.2) / h z.1) :=
    (hS.cont.comp continuous_mul).div (hS.cont.comp continuous_fst) (fun z => (hS.pos _).ne')
  obtain ⟨B, hB⟩ := (hC.prod hV).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨B, fun g x hx => ?_⟩
  obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
  have hlaw := hS.law q hq c (c * x)
  have heq : h (q * c * x) / h (q * c) = h (c * x) / h c := by
    rw [div_eq_div_iff (hS.pos _).ne' (hS.pos _).ne', mul_assoc]
    linear_combination (-1 : ℝ) * hlaw
  rw [heq]
  have hb := hB (c, x) ⟨hc, hx⟩
  simp only [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

theorem local_null [IsTopologicalGroup G] [LocallyCompactSpace G] {P : Subgroup G}
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (hS : Setup P h mu) {ν : Measure (G ⧸ P)} [IsFiniteMeasure ν]
    (hInv : ∀ x, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν)
    {Ω : Set G} (hΩ : IsOpen Ω) (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (hF : Few P h mu Ω) (q0 : G ⧸ P) :
    ∃ W : Set (G ⧸ P), IsOpen W ∧ q0 ∈ W ∧ ν ({q | rp q ∉ Ω} ∩ W) = 0 := by
  classical
  obtain ⟨U, d, hUo, hgU, hUP, hfew⟩ := hF (rp q0)
  have hφ : Continuous (fun z : G × G => rp q0 * z.1 * z.2⁻¹) :=
    (continuous_const.mul continuous_fst).mul continuous_snd.inv
  have hmem : (fun z : G × G => rp q0 * z.1 * z.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : G), (1 : G)) :=
    hφ.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using hgU))
  obtain ⟨N0, hN0, N1, hN1, hsub⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨V, hV1, hVN1, hVc⟩ := local_compact_nhds hN1
  obtain ⟨B, hB⟩ := ratio_bound hS hVc
  have hNo : IsOpen (interior N0) := isOpen_interior
  have h1N : (1 : G) ∈ interior N0 := mem_interior_iff_mem_nhds.mpr hN0
  let U' : Set G := {y | ∃ p ∈ P, ∃ n ∈ interior N0, y = p * (rp q0 * n)}
  have hU'o : IsOpen U' := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨p, hp, n, hn, rfl⟩
    refine ⟨(fun z => (p * rp q0)⁻¹ * z) ⁻¹' interior N0, ?_, ?_, ?_⟩
    · intro z hz
      exact ⟨p, hp, (p * rp q0)⁻¹ * z, hz, by group⟩
    · exact hNo.preimage (continuous_const.mul continuous_id)
    · show (p * rp q0)⁻¹ * (p * (rp q0 * n)) ∈ interior N0
      simpa [mul_assoc] using hn
  have hU'P : ∀ p ∈ P, ∀ x ∈ U', p * x ∈ U' := by
    rintro p hp x ⟨p', hp', n, hn, rfl⟩
    exact ⟨p * p', P.mul_mem hp hp', n, hn, (mul_assoc _ _ _).symm⟩
  have hgU' : rp q0 ∈ U' := ⟨1, P.one_mem, 1, h1N, by simp⟩
  have hshift : ∀ y ∈ U', ∀ γ ∈ V, y * γ⁻¹ ∈ U := by
    rintro y ⟨p, hp, n, hn, rfl⟩ γ hγ
    have h1 := hsub (Set.mk_mem_prod (interior_subset hn) (hVN1 hγ))
    simp only [Set.mem_preimage] at h1
    have h2 := hUP p hp _ h1
    simpa [mul_assoc] using h2
  refine ⟨{q | rp q ∈ U'}, isOpen_rp P hU'o hU'P, hgU', ?_⟩
  have hopenU : IsOpen {q : G ⧸ P | rp q ∈ U} := isOpen_rp P hUo hUP
  have hopenΩ0 : IsOpen {q : G ⧸ P | rp q ∈ Ω} := isOpen_rp P hΩ hP
  have hopenR : ∀ (S : Set G), IsOpen S → (∀ p ∈ P, ∀ x ∈ S, p * x ∈ S) → ∀ γ : G,
      IsOpen {q : G ⧸ P | rp q * γ ∈ S} := fun S hSo hSP γ =>
    isOpen_rp P (hSo.preimage (continuous_mul_const γ)) (fun p hp x hx => by
      show p * x * γ ∈ S
      rw [mul_assoc]
      exact hSP p hp _ hx)
  let A : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ U} ∩ {q | rp q * γ ∈ Ω}ᶜ
  let E' : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ Ω}ᶜ ∩ {q | rp q * γ⁻¹ ∈ U}
  have hAm : ∀ γ, MeasurableSet (A γ) := fun γ =>
    hopenU.measurableSet.inter (hopenR Ω hΩ hP γ).measurableSet.compl
  have hE'm : ∀ γ, MeasurableSet (E' γ) := fun γ =>
    hopenΩ0.measurableSet.compl.inter (hopenR U hUo hUP γ⁻¹).measurableSet
  have hEsub : ∀ γ ∈ V, {q | rp q ∉ Ω} ∩ {q | rp q ∈ U'} ⊆ E' γ := by
    rintro γ hγ q ⟨hq1, hq2⟩
    exact ⟨hq1, hshift _ hq2 γ hγ⟩
  have htrans : ∀ γ q, γ⁻¹ • q ∈ E' γ → q ∈ A γ := by
    rintro γ q ⟨h1, h2⟩
    obtain ⟨p, hp, hrp⟩ := rp_smul P γ q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at h1 h2
    rw [hrp] at h1 h2
    refine ⟨?_, ?_⟩
    · have h3 := hUP p⁻¹ (P.inv_mem hp) _ h2
      show rp q ∈ U
      simpa [mul_assoc] using h3
    · show ¬ (rp q * γ ∈ Ω)
      intro h4
      exact h1 (hP p hp _ h4)
  have hfin : ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (measure_ne_top ν univ))
  by_contra hne
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_mul_gt hne hfin
  obtain ⟨γ, hγ, hcnt⟩ := hfew V hV1 M
  have hstep : ∀ j, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ENNReal.ofReal B * ν (A (γ j)) := by
    intro j
    have hI := hInv (γ j) (hγ j).2 ((E' (γ j)).indicator 1) (measurable_one.indicator (hE'm _))
    calc ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ν (E' (γ j)) := measure_mono (hEsub _ (hγ j).1)
      _ = ∫⁻ q, (E' (γ j)).indicator 1 q ∂ν := (lintegral_indicator_one (hE'm _)).symm
      _ = ∫⁻ q, (E' (γ j)).indicator 1 ((γ j)⁻¹ • q) *
            ENNReal.ofReal (h (rp q * γ j) / h (rp q)) ∂ν := hI.symm
      _ ≤ ∫⁻ q, (A (γ j)).indicator 1 q * ENNReal.ofReal B ∂ν := by
          apply lintegral_mono
          intro q
          apply mul_le_mul'
          · simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;>
              first | exact le_rfl | exact zero_le | exact absurd (htrans _ _ h1) h2
          · exact ENNReal.ofReal_le_ofReal (hB _ _ (hγ j).1)
      _ = ν (A (γ j)) * ENNReal.ofReal B := by
          rw [lintegral_mul_const _ (measurable_one.indicator (hAm _)), lintegral_indicator_one (hAm _)]
      _ = ENNReal.ofReal B * ν (A (γ j)) := mul_comm _ _
  have hpt : ∀ q, ∑ j, (A (γ j)).indicator 1 q ≤ (d : ℝ≥0∞) := by
    intro q
    by_cases hq : rp q ∈ U
    · have hc := hcnt (rp q) hq
      have e : (↑(Finset.univ.filter (fun j => rp q * γ j ∉ Ω)) : Set (Fin M))
          = {j | rp q * γ j ∉ Ω} := by
        ext j
        simp
      rw [← e, Set.ncard_coe_finset] at hc
      calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q
          ≤ ∑ j, (if rp q * γ j ∉ Ω then (1 : ℝ≥0∞) else 0) := by
            apply Finset.sum_le_sum
            intro j _
            simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd h2 h1.2
        _ = ((Finset.univ.filter (fun j => rp q * γ j ∉ Ω)).card : ℝ≥0∞) := by
            rw [Finset.sum_boole]
        _ ≤ d := by exact_mod_cast hc
    · calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q = 0 :=
            Finset.sum_eq_zero (fun j _ => Set.indicator_of_notMem (fun h => hq h.1) _)
        _ ≤ d := zero_le
  have hsumA : ∑ j, ν (A (γ j)) ≤ (d : ℝ≥0∞) * ν univ := by
    calc ∑ j, ν (A (γ j)) = ∑ j, ∫⁻ q, (A (γ j)).indicator 1 q ∂ν :=
          Finset.sum_congr rfl (fun j _ => (lintegral_indicator_one (hAm _)).symm)
      _ = ∫⁻ q, ∑ j, (A (γ j)).indicator 1 q ∂ν :=
          (lintegral_finsetSum _ (fun j _ => measurable_one.indicator (hAm _))).symm
      _ ≤ ∫⁻ _q, (d : ℝ≥0∞) ∂ν := lintegral_mono hpt
      _ = (d : ℝ≥0∞) * ν univ := lintegral_const _
  have hMle : (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
      ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by
    calc (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
        = ∑ _j : Fin M, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) := by simp
      _ ≤ ∑ j, ENNReal.ofReal B * ν (A (γ j)) := Finset.sum_le_sum (fun j _ => hstep j)
      _ = ENNReal.ofReal B * ∑ j, ν (A (γ j)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by gcongr
  exact absurd hM (not_lt.mpr hMle)

theorem nullC_of_invM : InvM → NullC := by
  intro hInvM
  unfold NullC ForSet
  intro G _ _ _ _ _ _ P _ _ h mu hS ν hRepr Ω hΩ hP hF
  have : IsFiniteMeasure ν := hRepr.1
  have hInv : ∀ x : G, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν :=
    fun x hx => (hInvM G P h mu hS ν hRepr x hx).2
  apply measure_null_of_locally_null
  intro q0 _
  obtain ⟨W, hWo, hq0W, hWnull⟩ := local_null hS hInv hΩ hP hF q0
  exact ⟨{q | rp q ∉ Ω} ∩ W, inter_mem_nhdsWithin _ (hWo.mem_nhds hq0W), hWnull⟩

end GlobalTheory.CompanionTheory.RswCell.NullCompl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainVolume
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem ae_exists_smul_mem_image_prod :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ᵐ p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)), ∃ γ : Γ, γ • p ∈ (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕
  rw [(GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι).measurableEmbedding.ae_map_iff]
  have hcov : ∀ᵐ z ∂(ν.prod μ₁), ∃ γ₁ : Γ₁, γ₁ • z.2 ∈ 𝓕₁ :=
    Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers
  filter_upwards [hcov] with z hz
  obtain ⟨m, u⟩ := z
  obtain ⟨γ₁, hγ₁⟩ := hz
  obtain ⟨δ, hδ, -⟩ := hD (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) *
    MulAut.conjNormal (ι (π (ι γ₁))) m)
  have hδΓ : ((δ : π.ker) : P) ∈ Γ := Subgroup.mem_subgroupOf.mp δ.2
  refine ⟨⟨((δ : π.ker) : P) * ι γ₁, Γ.mul_mem hδΓ (hΓ γ₁ γ₁.2)⟩,
    ⟨(δ • (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) * MulAut.conjNormal (ι (π (ι γ₁))) m),
      γ₁ • u), ⟨hδ, hγ₁⟩, ?_⟩⟩
  simp only [GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply, Subgroup.smul_def, smul_eq_mul,
    Subgroup.coe_mul]
  rw [mul_assoc (((δ : π.ker) : P)) (ι (γ₁ : G₁)), GlobalTheory.CompanionTheory.SplitExtLat.mul_split ι π hπι (ι γ₁) m u,
    hπι, Subgroup.coe_mul, mul_assoc]

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_le_rev_eq_prod_ge : ∀ {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h), ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a) = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  first | exact @GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | exact GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | (intros; apply GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdRelIndexNeZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_rel_index_ne_zero : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂), I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | exact GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero <;> assumption)
end

