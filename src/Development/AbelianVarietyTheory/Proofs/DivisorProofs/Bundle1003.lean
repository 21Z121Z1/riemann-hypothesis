import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaConjUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramCharUnique

theorem eq_one_of_loc {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

theorem loc_parts {D : D7} {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (k : D.host.E)
    (hk : P.valuation D.host.E k ≤ 1) : infPart D (locE D e k) = 1 ∧ finPart D (locE D e k) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), (hint _).2 fun Q => ?_⟩
  have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := hι k
  have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (algebraMap D.host.E _ k - 1) := by
    rw [← h4]
    exact HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel, GlobalTheory.CharLocProd.val_algebraMap]
    exact hk
  · rw [h3 Q hQ, zero_mul, add_zero, map_one]

noncomputable def locHom {D : D7} {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun k => locE D e (k : D.host.E)
      map_one' := by simp [locE]
      map_mul' := fun k l => (locE_mul_locE he k l).symm }

theorem eq_one_of_unif {D : D7} {c : (AE D)ˣ →* Circle} (hc : IsHeckeChar D c) (hu : UnramEverywhere D c)
    (h : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ x : (AE D)ˣ,
      (x : AE D) = locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) → c x = 1) (x : (AE D)ˣ) : c x = 1 := by
  refine eq_one_of_loc ⟨hc, fun P e he k y hy => ?_⟩ x
  obtain rfl : y = locHom he.1 k := Units.ext hy
  have hπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) :=
    (GlobalTheory.CharLocProd.val_algebraMap P _).symm.trans (Formalism.L2.Host.unif_spec P)
  have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, P.valuation D.host.E (k : D.host.E) = WithZero.exp n := ⟨_, (WithZero.exp_log h0).symm⟩
  let u : D.host.Eˣ := k * Formalism.L2.Host.unif P ^ n
  have hv : P.valuation D.host.E (u : D.host.E) = 1 := by
    simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hn, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hv' : P.valuation D.host.E ((u⁻¹ : D.host.Eˣ) : D.host.E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  have h1 : c (locHom he.1 u) = 1 :=
    hu _ (loc_parts he _ hv.le).1 (loc_parts he _ hv.le).2 (by
      rw [← map_inv]
      exact (loc_parts he _ hv'.le).2)
  rw [map_mul, map_mul, map_zpow, map_zpow, h P e he (locHom he.1 (Formalism.L2.Host.unif P)) rfl, one_zpow, mul_one] at h1
  rw [h1]
  rfl

theorem isEtaConj_unique : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (η η' η'' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η'' → η' = η'' := by
  rintro D σ η η' η'' ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_unif (c := η' * η''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y a b c => mul_inv_eq_one.2 ((h2 y a b c).trans (g2 y a b c).symm))
    (fun P e he y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h3 P e he y hy
  obtain ⟨b, hb, hb'⟩ := g3 P e he y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.trans hb.symm)
  have : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hpos : (0 : ℝ) < (Nat.card (kP P) : ℝ) := Nat.cast_pos.2 Nat.card_pos
  exact Subtype.ext (mul_right_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 hpos).ne'))
    (ha'.symm.trans hb'))

end GlobalTheory.UnramCharUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
section
open MvPolynomial Filter

namespace GlobalTheory

namespace SatHilb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι K : Type*} [Field K]

end SatHilb

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma homogeneousComponent_add_X_pow_mul {K : Type} [Field K] {N : ℕ} (j : Fin N) (m n : ℕ)
    (g : MvPolynomial (Fin N) K) :
    homogeneousComponent (n + m) (X j ^ m * g) = X j ^ m * homogeneousComponent n g := by
  conv_lhs => rw [← sum_homogeneousComponent g, Finset.mul_sum, map_sum]
  have hterm : ∀ i, homogeneousComponent (n + m) (X j ^ m * homogeneousComponent i g) =
      if n + m = m + i then X j ^ m * homogeneousComponent i g else 0 := fun i =>
    homogeneousComponent_of_mem
      (((isHomogeneous_X_pow j m).mul (homogeneousComponent_isHomogeneous i g)))
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp [add_comm]
  · intro i _ hi
    rw [if_neg (by omega)]
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [homogeneousComponent_eq_zero n g (by omega), mul_zero, ite_self]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma homogeneousComponent_mem_of_isPrime_of_X_pow_saturation {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q := by
  by_cases hX : ∀ j, X j ∈ Q
  · have hspan : Ideal.span (X '' Set.univ) ≤ Q := by
      rw [Ideal.span_le]
      rintro _ ⟨j, -, rfl⟩
      exact hX j
    intro g hg n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hsub : g - C (coeff 0 g) ∈ Q := by
        apply hspan
        rw [mem_ideal_span_X_image]
        intro e he
        have he0 : e ≠ 0 := by
          rintro rfl
          simp at he
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
        exact ⟨i, Set.mem_univ _, hi⟩
      rw [homogeneousComponent_zero]
      have := Q.sub_mem hg hsub
      simpa using this
    · apply hspan
      rw [mem_ideal_span_X_image]
      intro e he
      rw [mem_support_iff, coeff_homogeneousComponent] at he
      have hdeg : e.degree = n := by
        by_contra hne
        exact he (if_neg hne)
      have he0 : e ≠ 0 := by
        rintro rfl
        simp at hdeg
        omega
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
      exact ⟨i, Set.mem_univ _, hi⟩
  · push_neg at hX
    obtain ⟨j, hj⟩ := hX
    intro g hg n
    obtain ⟨m, hm⟩ := hs g hg j
    have hmem := hIQ (hI _ hm (n + m))
    rw [homogeneousComponent_add_X_pow_mul] at hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact absurd (hQ.mem_of_pow_mem m h) hj
    · exact h

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∃ L : ℕ, ∀ n ≥ L, ∀ h ∈ Q, h ∈ homogeneousSubmodule (Fin N) K n → h ∈ I := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian Q : Q.FG)
  choose! mexp hmexp using hs
  set M := G.sup fun g => Finset.univ.sup (mexp g)
  set D := G.sup totalDegree
  set B := N * M + 1
  have hkey : ∀ g ∈ G, ∀ e : Fin N →₀ ℕ, B ≤ (e.sum fun _ k => k) → ∀ a : K,
      monomial e a * g ∈ I := by
    intro g hgG e he a
    have hgQ : g ∈ Q := hG ▸ Submodule.subset_span hgG
    have hj : ∃ j, M ≤ e j := by
      by_contra hne
      push_neg at hne
      have hsum : (e.sum fun _ k => k) ≤ N * M := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        calc ∑ j, e j ≤ ∑ _j : Fin N, M := Finset.sum_le_sum fun j _ => (hne j).le
          _ = N * M := by simp
      omega
    obtain ⟨j, hjM⟩ := hj
    have hle : mexp g j ≤ e j :=
      le_trans (le_trans (Finset.le_sup (f := mexp g) (Finset.mem_univ j))
        (Finset.le_sup (f := fun g => Finset.univ.sup (mexp g)) hgG)) hjM
    have hsingle : Finsupp.single j (mexp g j) ≤ e := by
      rw [Finsupp.single_le_iff]
      exact hle
    have hsplit : monomial e a =
        monomial (e - Finsupp.single j (mexp g j)) a * X j ^ mexp g j := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le hsingle]
    rw [hsplit, mul_assoc]
    exact I.mul_mem_left _ (hmexp g hgQ j)
  refine ⟨B + D, fun n hn h hQ hh => ?_⟩
  have hhn : h = homogeneousComponent n h := by
    rw [homogeneousComponent_of_mem hh, if_pos rfl]
  rw [← hG] at hQ
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hQ
  rw [hhn, ← hf, map_sum]
  refine I.sum_mem fun g hgG => ?_
  rw [smul_eq_mul, as_sum (f g), Finset.sum_mul, map_sum]
  refine I.sum_mem fun e _ => ?_
  by_cases hdeg : B ≤ (e.sum fun _ k => k)
  · exact hI _ (hkey g hgG e hdeg _) n
  · rw [homogeneousComponent_eq_zero]
    · exact I.zero_mem
    · have h1 := totalDegree_mul (monomial e (coeff e (f g))) g
      have h2 := totalDegree_monomial_le e (coeff e (f g))
      have h3 : g.totalDegree ≤ D := Finset.le_sup (f := totalDegree) hgG
      have h4 : (e.sum fun _ => id) = (e.sum fun _ k => k) := rfl
      omega

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma coe_decompose_homogeneousSubmodule_eq_homogeneousComponent {K : Type} [Field K] {N : ℕ}
    (g : MvPolynomial (Fin N) K) (n : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K)) =
      homogeneousComponent n g := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum,
    Finset.sum_eq_single n]
  · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
  · intro i _ hi
    exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g),
      homogeneousComponent_eq_zero n g (by omega)]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma isHomogeneous_of_forall_homogeneousComponent_mem {K : Type} [Field K] {N : ℕ}
    {I : Ideal (MvPolynomial (Fin N) K)} (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) I := by
  intro n g hg
  rw [coe_decompose_homogeneousSubmodule_eq_homogeneousComponent]
  exact hI g hg n

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem _root_.GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq (K : Type) [Field K] (N : ℕ)
    (I Q : Ideal (MvPolynomial (Fin N) K))
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧
      _root_.GlobalTheory.idealHilbertPoly Q = _root_.GlobalTheory.idealHilbertPoly I := by
  have hQh := homogeneousComponent_mem_of_isPrime_of_X_pow_saturation hI hQ hIQ hs
  refine ⟨hQh, ?_⟩
  obtain ⟨L, hL⟩ := exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous hI hs
  have hIh := isHomogeneous_of_forall_homogeneousComponent_mem hI
  have hQh' := isHomogeneous_of_forall_homogeneousComponent_mem hQh
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (((_root_.GlobalTheory.eventually_finrank_quotPiece hQh').and
      (_root_.GlobalTheory.eventually_finrank_quotPiece hIh)).and (eventually_ge_atTop L))
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n0 + n : ℕ) : ℚ))
    (fun a b hab => by simpa using hab) fun n => ?_
  obtain ⟨⟨hq, hi⟩, hLn⟩ := hn0 (n0 + n) (by omega)
  show Polynomial.eval _ _ = Polynomial.eval _ _
  rw [← hq, ← hi]
  have hint : Submodule.restrictScalars K Q ⊓ homogeneousSubmodule (Fin N) K (n0 + n) =
      Submodule.restrictScalars K I ⊓ homogeneousSubmodule (Fin N) K (n0 + n) := by
    apply le_antisymm
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hL (n0 + n) hLn h hh.1 hh.2, hh.2⟩
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hIQ hh.1, hh.2⟩
  have e1 := _root_.GlobalTheory.finrank_quotPiece_add Q (n0 + n)
  have e2 := _root_.GlobalTheory.finrank_quotPiece_add I (n0 + n)
  rw [hint] at e1
  congr 1
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulInt
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isIntegral_smul_of_charpoly_coeff_mul_int
    (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ)
    (h : ∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) :
    IsIntegral ℤ ((M : ℤ) • x) := by
  set χ := (LinearMap.mulLeft ℚ x).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _

  have hx : Polynomial.aeval x χ = 0 := by
    have h1 : Polynomial.aeval (LinearMap.mulLeft ℚ x) χ = 0 := LinearMap.aeval_self_charpoly _
    have h2 : Polynomial.aeval (Algebra.lmul ℚ A x) χ = Algebra.lmul ℚ A (Polynomial.aeval x χ) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h3 : Algebra.lmul ℚ A x = LinearMap.mulLeft ℚ x := rfl
    rw [h3, h1] at h2
    have := congrArg (fun f : A →ₗ[ℚ] A => f 1) h2
    simpa using this.symm
  have hs : Polynomial.aeval (algebraMap ℚ A (M : ℚ) * x) (χ.scaleRoots (M : ℚ)) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero hx
  have hsmon : (χ.scaleRoots (M : ℚ)).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    rw [Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero,
      mul_one]
    exact hmon
  have hlift : χ.scaleRoots (M : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy n χ.natDegree with hn | hn | hn
    · obtain ⟨a, ha⟩ := h n
      refine ⟨a * (M : ℤ) ^ (χ.natDegree - n - 1), ?_⟩
      have he : χ.natDegree - n = (χ.natDegree - n - 1) + 1 := by omega
      rw [he, pow_succ, map_mul, map_pow, eq_intCast, eq_intCast, ← ha]
      push_cast
      ring
    · subst hn
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by simpa using hmon.coeff_natDegree.symm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, -, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hsmon
  refine ⟨q, hqmon, ?_⟩
  have : Polynomial.aeval ((M : ℤ) • x) q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ, hq]
    convert hs using 2
    rw [Algebra.smul_def]
    simp
  simpa [Polynomial.aeval_def] using this

end GlobalTheory

example : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ), (∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) → IsIntegral ℤ ((M : ℤ) • x) := @GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotM
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ExtPrime

open MvPolynomial Filter in
open scoped ENNReal in

theorem _root_.GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L]
    [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K))
    (hP : P.IsPrime) :
    (P.map (MvPolynomial.map (algebraMap K L) :
      MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧
    ((∃ j, X j ∉ P) →
      (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
        MvPolynomial (Fin N) L) ∉
      P.map (MvPolynomial.map (algebraMap K L) :
        MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  classical
  haveI := hP
  let e := (commAlgEquiv K (Fin N) (Fin N)).toRingEquiv
  let ι : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K) :=
    MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K))
  let π : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K ⧸ P) :=
    (MvPolynomial.map (Ideal.Quotient.mk P)).comp e.toRingHom
  have heι : ∀ p, e (ι p) = C p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [e, ι, commAlgEquiv_C]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p i hp => rw [map_mul, map_mul, hp, map_X]; simp [e, commAlgEquiv_X]
  have hQ : P.map ι = RingHom.ker π := by
    ext b
    rw [RingHom.mem_ker]
    have hb : b = e.symm (e b) := (e.symm_apply_apply b).symm
    constructor
    · intro hb'
      have h1 : P.map ι ≤ RingHom.ker π := by
        rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show MvPolynomial.map (Ideal.Quotient.mk P) (e (ι p)) = 0
        rw [heι p, map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
      exact h1 hb'
    · intro hb'
      have hmem : e b ∈ Ideal.map C P := by
        have hk : Ideal.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) P =
            RingHom.ker (MvPolynomial.map (σ := Fin N) (Ideal.Quotient.mk P)) := by
          rw [MvPolynomial.ker_map, Ideal.mk_ker]
        rw [hk, RingHom.mem_ker]
        exact hb'
      rw [hb]
      have h2 : Ideal.map e.symm (Ideal.map C P) ≤ P.map ι := by
        rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro p hp
        have h4 : e.symm (C p) = ι p := by
          rw [← heι p]; exact e.symm_apply_apply _
        have h3 : e.symm (C p) ∈ P.map ι := by
          rw [h4]; exact Ideal.mem_map_of_mem ι hp
        exact h3
      exact h2 (Ideal.mem_map_of_mem _ hmem)
  have hQprime : (P.map ι).IsPrime := by rw [hQ]; exact RingHom.ker_isPrime π
  letI : Algebra (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L) :=
    (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).toAlgebra
  let Mₛ : Submonoid (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) :=
    Submonoid.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K))
      (nonZeroDivisors (MvPolynomial (Fin N) K))
  haveI hloc : IsLocalization Mₛ (MvPolynomial (Fin N) L) :=
    MvPolynomial.isLocalization (nonZeroDivisors (MvPolynomial (Fin N) K)) L
  have hdisj : Disjoint (Mₛ : Set (MvPolynomial (Fin N) (MvPolynomial (Fin N) K))) ↑(P.map ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    rw [SetLike.mem_coe, hQ, RingHom.mem_ker] at hrQ
    have hπ : π (C r) = MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K ⧸ P)) r := by
      simp only [π, RingHom.coe_comp, Function.comp_apply]
      rw [show e.toRingHom (C r) = MvPolynomial.map C r from commAlgEquiv_C (R := K) (S₁ := Fin N) r,
        MvPolynomial.map_map]
      rfl
    rw [hπ] at hrQ
    have hinj := MvPolynomial.map_injective (σ := Fin N) _
      (algebraMap K (MvPolynomial (Fin N) K ⧸ P)).injective
    have hr0 : r = 0 := hinj (by rw [hrQ, map_zero])
    exact nonZeroDivisors.ne_zero hr hr0
  have hcomp : (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)).comp ι := by
    refine RingHom.ext fun p => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, ι, RingHom.algebraMap_toAlgebra, MvPolynomial.map_map]
    rw [← IsScalarTower.algebraMap_eq]
  have hmapeq : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (P.map ι).map (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)) := by
    rw [hcomp, Ideal.map_map]
  rw [hmapeq]
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hQprime hdisj, ?_⟩
  rintro ⟨j, hj⟩ hG
  let G₀ : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) := ∑ i : Fin N, C (X i) * X i
  have hG₀ : algebraMap _ (MvPolynomial (Fin N) L) G₀ =
      ∑ i : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X i)) * X i := by
    simp [G₀, RingHom.algebraMap_toAlgebra, map_sum]
  rw [← hG₀] at hG
  have hG₀Q : G₀ ∈ P.map ι := by
    have h := IsLocalization.comap_map_of_isPrime_disjoint _ (MvPolynomial (Fin N) L) hQprime hdisj
    rw [← h]
    exact hG
  rw [hQ, RingHom.mem_ker] at hG₀Q
  have hπG : π G₀ = ∑ i : Fin N, X i * C (Ideal.Quotient.mk P (X i)) := by
    simp only [π, G₀, RingHom.coe_comp, Function.comp_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show e.toRingHom (C (X i)) = X i from commAlgEquiv_C_X (R := K) (S₁ := Fin N) i,
      show e.toRingHom (X i) = C (X i) from commAlgEquiv_X (R := K) (S₂ := Fin N) i, map_X, map_C]
  rw [hπG] at hG₀Q
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hG₀Q
  simp only [coeff_sum, coeff_zero] at hcoeff
  simp_rw [mul_comm (X _), coeff_C_mul, coeff_X', Finsupp.single_left_inj one_ne_zero] at hcoeff
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hcoeff
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)

end GlobalTheory.ExtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPoweStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w a, g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  first | exact @GlobalTheory.IwasawaGL.iwasawa_diagPow | exact GlobalTheory.IwasawaGL.iwasawa_diagPow | (intros; apply GlobalTheory.IwasawaGL.iwasawa_diagPow <;> assumption)
end

