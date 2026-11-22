import Mathlib
import GroundTheory.Brauer.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
section
open Module Polynomial TensorProduct

namespace GlobalTheory.CentSep

theorem aeval_mem_span_pow {K S : Type} [Field K] [Ring S] [Nontrivial S] [Algebra K S] (x : S)
    (hx : IsIntegral K x) (q : K[X]) :
    aeval x q ∈ Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
  have hm := minpoly.monic hx
  rw [← aeval_modByMonic_eq_self_of_root (p := q) (minpoly.aeval K x)]
  have hne : minpoly K x ≠ 1 := by
    intro h
    have := minpoly.natDegree_pos hx
    rw [h, natDegree_one] at this
    exact lt_irrefl _ this
  have hlt := natDegree_modByMonic_lt q hm hne
  rw [aeval_eq_sum_range' hlt]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨j, Finset.mem_range.mp hj⟩, rfl⟩)

theorem centralizer_toSubmodule {K S : Type} [Field K] [Ring S] [Algebra K S] (g : S) :
    Subalgebra.toSubmodule (Subalgebra.centralizer K ({g} : Set S)) =
      LinearMap.ker (LinearMap.mulLeft K g - LinearMap.mulRight K g) := by
  ext y
  simp [Subalgebra.mem_centralizer_iff, sub_eq_zero]

theorem natDegree_minpoly_le_baseChange {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem centralizer_eq_adjoin : ∀ (F B : Type) [Field F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ g : B, (minpoly F g).Separable →
      (minpoly F g).natDegree = n → Subalgebra.centralizer F {g} = Algebra.adjoin F {g} := by
  intro F B _ _ _ _ _ _ n hB g hsep hdeg
  classical
  obtain ⟨k, hk0, hkB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkB.symm.trans hB)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] B := (1 : K) ⊗ₜ[F] g with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x

  have hxr : x = Algebra.TensorProduct.includeRight g := rfl
  have hdvd : minpoly K x ∣ (minpoly F g).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_baseChange K g hxi
  rw [hdeg] at hge
  have hle : (minpoly K x).natDegree ≤ k := by
    have hmap : (minpoly F g).map (algebraMap F K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero (IsIntegral.of_finite F g))
    calc (minpoly K x).natDegree ≤ ((minpoly F g).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = k := by rw [natDegree_map, hdeg]
  have hxdeg : (minpoly K x).natDegree = k := le_antisymm hle hge

  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hchar : N.charpoly = minpoly K x := by
    have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
    rw [hmN] at hd
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hd
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hxdeg])
    rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul]
  have hNsep : N.charpoly.Separable := by
    rw [hchar]
    exact (hsep.map).of_dvd hdvd

  have hCK : Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))) ≤
      Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
    intro y hy
    have hy' : x * y = y * x :=
      (Subalgebra.mem_centralizer_iff K).mp hy x (Set.mem_singleton x)
    have hcomm : Commute (e y) N := by
      change e y * e x = e x * e y
      rw [← map_mul, ← map_mul, hy']
    obtain ⟨q, hq⟩ := GlobalTheory.T.matrix_eq_aeval_of_commute_of_charpoly_separable k N (e y) hNsep hcomm
    have : y = aeval x q := by
      apply e.injective
      rw [hq, hN, ← aeval_algHom_apply]
    rw [this]
    exact aeval_mem_span_pow x hxi q
  have hfinK : finrank K (Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))))
      ≤ k := by
    calc _ ≤ finrank K (Submodule.span K
            (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ))) :=
          Submodule.finrank_mono hCK
      _ ≤ Fintype.card (Fin (minpoly K x).natDegree) := finrank_range_le_card _
      _ = k := by rw [Fintype.card_fin, hxdeg]

  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange F K B (K ⊗[F] B) Unit
    (TensorProduct.mk F K B 1) (TensorProduct.isBaseChange F B K)
    (fun _ => LinearMap.mulLeft F g - LinearMap.mulRight F g)
    (fun _ => LinearMap.mulLeft K x - LinearMap.mulRight K x)
    (fun _ v => by
      simp [hx, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).1
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  rw [← centralizer_toSubmodule, ← centralizer_toSubmodule] at hbc

  have hadj : Algebra.adjoin F ({g} : Set B) ≤ Subalgebra.centralizer F {g} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_centralizer_iff F).mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]))
  have hspan : Submodule.span F (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton g)) _
  have hfinS : k ≤ finrank F (Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B))) := by
    calc k = Fintype.card (Fin (minpoly F g).natDegree) := by rw [Fintype.card_fin, hdeg]
      _ = finrank F (Submodule.span F
            (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ))) :=
          (finrank_span_eq_card (linearIndependent_pow g)).symm
      _ ≤ _ := Submodule.finrank_mono hspan
  have heq := Submodule.eq_of_le_of_finrank_le
    (Subalgebra.toSubmodule.monotone hadj) (by rw [← hbc]; exact hfinK.trans hfinS)
  exact (Subalgebra.toSubmodule_injective heq).symm

end GlobalTheory.CentSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairResBijectiveTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open FormExt FormExtJ

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem pairRes_bijective_two {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : Function.Bijective (pullHyp2 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'

  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') (pairFst φ) H hcov hdir

  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have unitE : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  have HE := hasLoc_omExt (OAff s') H
  have hcovE : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omExt (OAff s')) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unitE u _ hu)⟩
  have hdirE : ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omExt (OAff s')) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unitE u _ hu)⟩
  have hsE := _root_.GlobalTheory.sep_of_factoring_cover (omExt (OAff s')) (pairFst φ) HE hcovE
  have hgE := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE
  have hvE := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE

  have hcovJ : ∀ j : ℕ, ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omjExt (OAff s') j) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun j T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S u hu ↦ h i S u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hdirJ : ∀ j : ℕ, ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omjExt (OAff s') j) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun j t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S' u hu ↦ h i S' u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hsJ := fun j ↦ _root_.GlobalTheory.sep_of_factoring_cover (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j)
  have hgJ := fun j ↦ _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j) (hdirJ j)
  have hs3 : ∀ (T : AffOp X') (x : Om R' ((OAff s').obj T) 3),
      (∀ t (u : T ⟶ (pairFst φ).obj t), pOm (OAff s') 3 u x = 0) → x = 0 := by
    intro T x hx
    have h0 : (TrivSqZeroExt.inr x : (omjExt (OAff s') 3).obj T) = 0 :=
      hsJ 3 T _ fun t u ↦ (mp_omjExt_inr (OAff s') 3 u x).trans (by rw [hx t u]; exact TrivSqZeroExt.inr_zero _)
    simpa using congrArg TrivSqZeroExt.snd h0

  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  refine ⟨GlobalTheory.T.comma_first_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_injective _ _ hs hg hv) b1.2
      (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2,
    GlobalTheory.T.comma_second_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2)
      (GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict _ _ (GlobalTheory.T.comma_descent_injective _ _ hsE hgE hvE))
      (GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary _ _ (_root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hsE hgE hvE))
      (GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict _ _ 2 (_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ (hsJ 2) (hgJ 2)))
      (GlobalTheory.T.compatible_higherForms_extend_along_functor _ _ 2 (hsJ 2) (hgJ 2)) hs3⟩

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem existsUnique_isPull2 (c : HH2 s) : ∃! c', IsPull2 h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective_two φ s').existsUnique (pullHyp2 (pairPull h) c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

def pairResEquiv2 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH2 s' ≃ₗ[R'] Hyp2 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp2 (pairRes φ s')) (pairRes_bijective_two φ s')

def pullHH2 : HH2 s →ₛₗ[σ] HH2 s' :=
  (pairResEquiv2 φ s').symm.toLinearMap.comp (pullHyp2 (pairPull h))

theorem isPull2_pullHH2 (c : HH2 s) : IsPull2 h c (pullHH2 h c) :=
  ((pairResEquiv2 φ s').apply_symm_apply _).symm

theorem IsPull2.eq_pullHH2 {c : HH2 s} {c' : HH2 s'} (e : IsPull2 h c c') : c' = pullHH2 h c :=
  (existsUnique_isPull2 h c).unique e (isPull2_pullHH2 h c)

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectoidTowerSurjective
section
open Ideal WittVector

namespace GlobalTheory

theorem pflat_dvd_of_roots : ∀ (p : ℕ) [Fact p.Prime] (A R : Type) [CommRing A] [IsDomain A] [CommRing R]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R] (φ : A →+* R), (p : A) ≠ 0 →
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) →
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) = Ideal.span {(p : A)} →
    ∀ π : ℕ → A, π 0 = p → (∀ n, π (n + 1) ^ p = π n) → (∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x) →
    ∃ pflat : PreTilt R p, PreTilt.untilt pflat = (p : R) ∧ ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c := by
  intro p hp A R _ _ _ _ _ φ hp0 hsurj hker π hπ0 hπ hdiv
  classical
  have hpp : p.Prime := hp.out
  have : CharP (R ⧸ Ideal.span {(p : R)}) p := (inferInstance : CharP (ModP R p) p)
  set g := (Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ with hg
  have hf : ∀ n, φ (π (n + 1)) ^ p = φ (π n) := fun n => by rw [← map_pow, hπ]
  refine ⟨ReciprocityTheory.PGsh.ofRoots (fun n => φ (π n)) hf, ?_, ?_⟩
  · rw [ReciprocityTheory.PGsh.untilt_ofRoots, hπ0, map_natCast]
  intro c hc
  have hz : ∀ x, g x = 0 ↔ (p : A) ∣ x := fun x => by
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
  have hππ : ∀ n, π n ^ p ^ n = p := by
    intro n
    induction n with
    | zero => simp [hπ0]
    | succ n ih => rw [pow_succ', pow_mul, hπ, ih]
  have hcs : ∀ n, Perfection.coeff (ModP R p) p (n + 1) c ^ p = Perfection.coeff (ModP R p) p n c :=
    fun n => Perfection.coeff_pow_p' c n
  have hc0 : Perfection.coeff (ModP R p) p 0 c = 0 := by rw [← PreTilt.coeff_def]; exact hc
  have hcp : ∀ n, Perfection.coeff (ModP R p) p n c ^ p ^ n = 0 := by
    intro n
    induction n with
    | zero => simpa using hc0
    | succ n ih => rw [pow_succ', pow_mul, hcs, ih]
  choose y hy using fun n => hsurj (show R ⧸ Ideal.span {(p : R)} from Perfection.coeff (ModP R p) p n c)
  have hyp : ∀ n, (p : A) ∣ y n ^ p ^ n := fun n => (hz _).1 (by rw [map_pow, hy]; exact hcp n)
  choose z hzy using fun n => hdiv n (y n) (hyp n)
  have compat : ∀ n, g (z (n + 2) ^ p) ^ p = g (z (n + 1) ^ p) := by
    intro n
    set b := z (n + 2) ^ p - z (n + 1) with hb
    have h1 : π (n + 1) * b = y (n + 2) ^ p - y (n + 1) := by
      rw [hzy (n + 2), hzy (n + 1), mul_pow, hπ (n + 1), hb]; ring
    have h2 : g (π (n + 1) * b) = 0 := by
      rw [h1, map_sub, map_pow, hy, hy]
      exact sub_eq_zero.2 (hcs (n + 1))
    obtain ⟨w, hw⟩ := (hz _).1 h2
    have e1 : π n * b ^ p = (p : A) ^ p * w ^ p := by rw [← hπ n, ← mul_pow, hw, mul_pow]
    have hp2 : (p : A) ^ p = (p : A) ^ (p - 2) * (p : A) ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hpp.two_le]
    have hn1 : π n ^ p ^ n = π n ^ (p ^ n - 1) * π n := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hpp.pos)]
    have e2 : (p : A) * b ^ p = (p : A) * ((p : A) * ((p : A) ^ (p - 2) * w ^ p * π n ^ (p ^ n - 1))) := by
      calc (p : A) * b ^ p = π n ^ p ^ n * b ^ p := by rw [hππ]
        _ = π n ^ (p ^ n - 1) * (π n * b ^ p) := by rw [hn1]; ring
        _ = _ := by rw [e1, hp2]; ring
    have hbp : g (b ^ p) = 0 := (hz _).2 ⟨_, mul_left_cancel₀ hp0 e2⟩
    have hz2 : z (n + 2) ^ p = z (n + 1) + b := by rw [hb]; ring
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hz2, map_pow, map_add, add_pow_char, ← map_pow g b, hbp,
      add_zero, map_pow]
  let d : PreTilt R p := ⟨fun n => g (z (n + 1) ^ p), fun n => compat n⟩
  refine ⟨d, Perfection.ext fun n => ?_⟩
  show Perfection.coeff (ModP R p) p n c = g (π n) * g (z (n + 1) ^ p)
  rw [← map_mul, ← hπ n, ← mul_pow, ← hzy (n + 1), map_pow, hy, hcs]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageConnectedComponentRationalPointFieldExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  first | exact @GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange | exact GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange | (intros; apply GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

section One
variable {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]

theorem isHomeomorph : IsHomeomorph i :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩

def upOpen (U : Y₀.Opens) : Y₁.Opens := ⟨i '' (U : Set Y₀), (isHomeomorph i).isOpenMap _ U.2⟩

theorem preimage_upOpen (U : Y₀.Opens) : i ⁻¹ᵁ upOpen i U = U := by
  ext x
  change i x ∈ i '' (U : Set Y₀) ↔ x ∈ U
  exact (isHomeomorph i).injective.mem_set_image

theorem upOpen_preimage (V : Y₁.Opens) : upOpen i (i ⁻¹ᵁ V) = V := by
  ext y
  change y ∈ i '' (i ⁻¹' (V : Set Y₁)) ↔ y ∈ V
  rw [Set.image_preimage_eq _ i.surjective]
  rfl

theorem upOpen_mono : Monotone (upOpen i) := fun _ _ h ↦ Set.image_mono h

abbrev upFun : Y₀.Opens ⥤ Y₁.Opens := (upOpen_mono i).functor

def res (U : Y₀.Opens) : Γ(Y₁, upOpen i U) ⟶ Γ(Y₀, U) :=
  i.appLE (upOpen i U) U (preimage_upOpen i U).ge

theorem res_naturality {U V : Y₀.Opens} (h : U ≤ V) :
    Y₁.presheaf.map (homOfLE (upOpen_mono i h)).op ≫ res i U =
      res i V ≫ Y₀.presheaf.map (homOfLE h).op := by
  simp only [res, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end One

section Two
variable {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁]
  [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂]

abbrev cone (U : Y₀.Opens) : PullbackCone (res i₁ U) (res i₂ U) :=
  CommRingCat.pullbackCone (res i₁ U) (res i₂ U)

def coneIsLimit (U : Y₀.Opens) : IsLimit (cone i₁ i₂ U) :=
  CommRingCat.pullbackConeIsLimit _ _

def fibMap {U V : Y₀.Opens} (h : U ≤ V) : (cone i₁ i₂ V).pt ⟶ (cone i₁ i₂ U).pt :=
  PullbackCone.IsLimit.lift (coneIsLimit i₁ i₂ U)
    ((cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op)
    ((cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op)
    (by rw [Category.assoc, Category.assoc, res_naturality i₁ h, res_naturality i₂ h,
      (cone i₁ i₂ V).condition_assoc])

@[reassoc (attr := simp)]
theorem fibMap_fst {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).fst =
    (cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem fibMap_snd {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).snd =
    (cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

def fib : Y₀.Opensᵒᵖ ⥤ CommRingCat.{0} where
  obj U := (cone i₁ i₂ U.unop).pt
  map f := fibMap i₁ i₂ f.unop.le
  map_id U := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ U.unop)
    (by simp [homOfLE_refl]) (by simp [homOfLE_refl])
  map_comp f g := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ _)
    (by simp [← Functor.map_comp]; rfl) (by simp [← Functor.map_comp]; rfl)

def fibFst : fib i₁ i₂ ⟶ (upFun i₁).op ⋙ Y₁.presheaf where
  app U := (cone i₁ i₂ U.unop).fst
  naturality U V f := fibMap_fst i₁ i₂ f.unop.le

def fibSnd : fib i₁ i₂ ⟶ (upFun i₂).op ⋙ Y₂.presheaf where
  app U := (cone i₁ i₂ U.unop).snd
  naturality U V f := fibMap_snd i₁ i₂ f.unop.le

def fibπ : fib i₁ i₂ ⟶ Y₀.presheaf where
  app U := (cone i₁ i₂ U.unop).fst ≫ res i₁ U.unop
  naturality U V f := by
    change fibMap i₁ i₂ f.unop.le ≫ _ ≫ _ = _
    rw [fibMap_fst_assoc, res_naturality]
    rfl

def good : Set Y₀.Opens :=
  {U | IsAffineOpen U ∧ IsAffineOpen (upOpen i₁ U) ∧ IsAffineOpen (upOpen i₂ U)}

end Two

end GlobalTheory.FerrandPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDegreeOfNotMemFilTwo
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC

namespace GlobalTheory

theorem prod_mem_Fil_zero_of_factors {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {ι : Type}
    (s : Finset ι) (x : ι → P.R.BdR) (h : ∀ i ∈ s, x i ∈ (P.PD K).Fil 0) :
    (∏ i ∈ s, x i) ∈ (P.PD K).Fil 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (P.PD K).one_mem
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := (P.PD K).Fil_mul 0 0 _ _ (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1

theorem prod_degree_of_not_mem_Fil_two : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {ι : Type} (s : Finset ι) (x : ι → P.R.BdR) (i₀ : ι), i₀ ∈ s →
    (∀ i ∈ s, x i ∈ (P.PD K).Fil 0) → x i₀ ∈ (P.PD K).Fil 1 → (∏ i ∈ s, x i) ∉ (P.PD K).Fil 2 →
    x i₀ ∉ (P.PD K).Fil 2 ∧ ∀ i ∈ s, i ≠ i₀ → x i ∉ (P.PD K).Fil 1 := by
  classical
  intro l _ P K ι s x i₀ hi₀ h0 h1 hprod
  have hrest : (∏ i ∈ s.erase i₀, x i) ∈ (P.PD K).Fil 0 :=
    prod_mem_Fil_zero_of_factors P K _ x fun i hi => h0 i (Finset.mem_of_mem_erase hi)
  refine ⟨fun h2 => hprod ?_, fun i hi hne h1i => hprod ?_⟩
  · rw [← Finset.mul_prod_erase s x hi₀]
    simpa using (P.PD K).Fil_mul 2 0 _ _ h2 hrest
  · have hi' : i ∈ s.erase i₀ := Finset.mem_erase.mpr ⟨hne, hi⟩
    have hrest2 : (∏ j ∈ (s.erase i₀).erase i, x j) ∈ (P.PD K).Fil 0 :=
      prod_mem_Fil_zero_of_factors P K _ x fun j hj =>
        h0 j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))
    have hA : x i * (∏ j ∈ (s.erase i₀).erase i, x j) ∈ (P.PD K).Fil 1 := by
      simpa using (P.PD K).Fil_mul 1 0 _ _ h1i hrest2
    rw [← Finset.mul_prod_erase s x hi₀, ← Finset.mul_prod_erase (s.erase i₀) x hi']
    simpa [one_add_one_eq_two] using (P.PD K).Fil_mul 1 1 _ _ h1 hA

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurEquivariantIsometryScalarStatement
section
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_equivariant_isometry_scalar : ∀ (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l), (∀ w v, U (rho w v) = rho w (U v)) →
    ∃ a : ℂ, ∀ v, U v = a • v := by
  first | exact @GlobalTheory.RealWeil.schur_rho_l2 | exact GlobalTheory.RealWeil.schur_rho_l2 | (intros; apply GlobalTheory.RealWeil.schur_rho_l2 <;> assumption)
end

