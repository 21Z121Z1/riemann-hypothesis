import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.PointConditions

theorem sum_single_jumps {M : Type} [AddCommMonoid M] [One M] (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : M) else 0)) = if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    rw [Finset.sum_eq_single (n + 1)]
    · rw [if_pos (by push_cast; ring)]
    · intro c _ hne
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem isSSRep_rhoChiK (D : D7) (i : D.nd.Loc) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.BlockSemisimple ρ (D.nd.chi i) D.R.t) : IsSSRep (rhoChiK D i ρ) := by
  rw [GlobalTheory.ComplementCompare.isSSRep_iff]
  refine (GlobalTheory.ComplementCompare.semisimple_congr (splitRT (KK D.nd i) D.R.r D.R.t) ?_).2 h
  intro g v
  change splitRT _ _ _ (((rhoChiK D i ρ g : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) :
      Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec v) = _
  unfold rhoChiK
  rw [blockRep_coe, blockHom_mulVec, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply]
  refine Prod.ext rfl (funext fun c => ?_)
  show (Matrix.diagonal _).mulVec _ c = _
  rw [Matrix.mulVec_diagonal]
  rfl

theorem main : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (ρ i π) ∧ IsSSRep (rhoChiK D i (ρ i π)) ∧ EmbeddingTypes.ambBlock i (r i) (ρ i) π ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π := by
  intro D r ρ h i π hπ
  have hc := h.compl i π hπ
  refine ⟨h.frob i π hπ, isSSRep_rhoChiK D i (ρ i π) hc.ss, ?_, ?_⟩
  · intro _ _ _ w hw C τ
    have hB := h.block i π hπ w hw C.LL C.le τ
    refine ⟨fun a => ?_, fun c hc a => hB.2 c hc a⟩
    have h2 : ∀ c ∈ Finset.Icc 1 D.R.t, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0 := fun c hc => hB.2 c hc a
    rw [Finset.sum_congr rfl h2, sum_single_jumps]
    exact hB.1 a
  · obtain ⟨e, he⟩ := hc.rho
    refine ⟨e, fun g u => ?_⟩
    have := he g u
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply] at this
    exact this

end GlobalTheory.PointConditions
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eq_zero_of_mem_adI_pow {l : ℕ} {R : Type} [CommRing R] (B : Obj l R) (x : B.A)
    (hx : ∀ n : ℕ, x ∈ adI B ^ n) : x = 0 := by
  refine B.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact hx n

theorem cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C),
    Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q →
      ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  intro l _ R _ B C h hc

  have hinj : ∀ m : ℕ, Function.Injective (qmap h m) := fun m =>
    RingHom.FaithfullyFlat.injective (hc.ff m)

  have hlev : ∀ (m : ℕ) (b : B.A), h.f b ∈ adI C ^ m → b ∈ adI B ^ m := fun m b hb => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj m
    rw [qmap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  refine ⟨fun x y hxy => ?_, fun D p q hpo c hpq => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow B _ fun n => hlev n _ ?_
    rw [map_sub, hxy, sub_self]; exact Ideal.zero_mem _
  ·
    have happ : ∀ m : ℕ, ∃ b : B.A, h.f b - c ∈ adI C ^ m := fun m => by
      have hd := (GlobalTheory.T.faithfullyFlat_descent_elements_pushout _ _ _ (qmap h m) (qmap p m) (qmap q m) (hc.ff m) (hpo.po m)).2
        (Ideal.Quotient.mk _ c) (by rw [qmap_mk, qmap_mk, hpq])
      obtain ⟨b', hb'⟩ := hd
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      refine ⟨b, ?_⟩
      rw [qmap_mk, Ideal.Quotient.eq] at hb'
      exact hb'
    choose b hb using happ
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (adI B ^ m • ⊤ : Submodule B.A B.A)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      refine hlev m _ ?_
      have e : h.f (b m - b n) = (h.f (b m) - c) - (h.f (b n) - c) := by rw [map_sub]; ring
      rw [e]
      exact Ideal.sub_mem _ (hb m) (Ideal.pow_le_pow_right hmn (hb n))
    obtain ⟨L, hL⟩ := B.complete.toIsPrecomplete.prec' b hcauchy
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow C _ fun n => ?_
    have h1 : b n - L ∈ adI B ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    have h2 : h.f (b n - L) ∈ adI C ^ n := adI_pow_le h n h1
    have e : h.f L - c = (h.f (b n) - c) - h.f (b n - L) := by rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (hb n) h2

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangular
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EnvShape

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A]

theorem C_mem_supp (S : Set ℕ) (c : A) : MvPolynomial.C c ∈ MvPolynomial.supported A S := by
  rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ c

omit hl in

theorem cc_mem_ideal {R : Type} [CommRing R] (I : Ideal R) {x : R} (y : R) (hx : x ∈ I) : cc l x y ∈ I := by
  unfold cc
  exact Ideal.sum_mem _ fun k hk =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx k (Finset.mem_Ioo.1 hk).1))

omit hl in

theorem cc_mem_sub {R : Type} [CommRing R] [Algebra A R] (S : Subalgebra A R) {x y : R} (hx : x ∈ S)
    (hy : y ∈ S) : cc l x y ∈ S := by
  unfold cc
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hx _)) (S.pow_mem hy _)

theorem phi_mem (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) {e : A} (he : e ∈ J) : D.φ e ∈ J := by
  rw [D.φ_eq]; exact J.add_mem (J.pow_mem_of_mem he _ hl.out.pos) (J.mul_mem_right _ hlJ)

theorem delta_Iio (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) (i : ℕ) (s : MvPolynomial ℕ A)
    (hs : s ∈ MvPolynomial.supported A (Set.Iio i)) :
    (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic i) ∧
    ∃ a ∈ MvPolynomial.supported A (Set.Iio i), ∃ b ∈ MvPolynomial.supported A (Set.Iio i),
      (polyDelta D).δ s - (a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  cases i with
  | zero =>
    have h0 : Set.Iio (0:ℕ) = ∅ := by ext; simp
    rw [h0, MvPolynomial.supported_empty, Algebra.mem_bot] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨C_mem_supp _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ c), C_mem_supp _ _, ?_⟩
    simp
  | succ i =>
    have h1 : Set.Iio (i+1) = Set.Iic i := by ext; simp [Nat.lt_succ_iff]
    rw [h1] at hs ⊢
    obtain ⟨h2, a, ha, b, hb, h3⟩ := GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime l A D i s hs
    have hl' : (l : MvPolynomial ℕ A) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.C : A →+* MvPolynomial ℕ A) hlJ
      rwa [map_natCast] at this
    exact ⟨h2, a, ha, b, hb, Ideal.span_le.2 (Set.singleton_subset_iff.2 hl') h3⟩

theorem step_eq (D : Delta l A) (e : A) (k : ℕ) (s : MvPolynomial ℕ A) :
    (polyDelta D).δ (MvPolynomial.C e * MvPolynomial.X k + s) =
      MvPolynomial.C (D.φ e) * MvPolynomial.X (k + 1) +
        (MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
          cc l (MvPolynomial.C e * MvPolynomial.X k) s) := by
  rw [(polyDelta D).δ_add, (polyDelta D).δ_mul, polyDelta_C, polyDelta_X, D.φ_eq]
  simp only [map_add, map_pow, map_mul, map_natCast]
  unfold cc; ring

theorem shape (D : Delta l A) (J : Ideal A) (d p : A) (hlJ : (l : A) ∈ J) (hd : d ∈ J)
    (hu : IsUnit (D.δ d)) (k : ℕ) :
    ∃ e ∈ J, IsUnit (D.δ e) ∧ ∃ s ∈ MvPolynomial.supported A (Set.Iio k),
      (polyDelta D).δ^[k] (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) =
        MvPolynomial.C e * MvPolynomial.X k + s := by
  induction k with
  | zero => exact ⟨d, hd, hu, MvPolynomial.C p, C_mem_supp _ _, by simp [add_comm]⟩
  | succ k ih =>
    obtain ⟨e, he, heu, s, hs, hk⟩ := ih
    have hIic : Set.Iic k = Set.Iio (k+1) := by ext; simp [Nat.lt_succ_iff]
    have hX : MvPolynomial.X k ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      by rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨k, by simp, rfl⟩
    have hδ := (delta_Iio D J hlJ k s hs).1
    rw [hIic] at hδ
    have hs' : s ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      MvPolynomial.supported_mono (Set.Iio_subset_Iio (Nat.le_succ k)) hs
    refine ⟨D.φ e, phi_mem D J hlJ he, ?_, MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
      cc l (MvPolynomial.C e * MvPolynomial.X k) s, ?_, ?_⟩
    · rw [GlobalTheory.T.deltaRingStructure_delta_frobenius_comm]; exact heu.map D.φ
    · exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hX _)
        (C_mem_supp _ _)) hδ) (cc_mem_sub _ (Subalgebra.mul_mem _ (C_mem_supp _ _) hX) hs')
    · rw [Function.iterate_succ_apply', hk, step_eq]

theorem envRel_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A),
    a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧
    envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈
      J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  intro l _ A _ D J d p hlJ hd hu i
  obtain ⟨e, he, heu, s, hs, hi⟩ := shape D J d p hlJ hd hu i
  obtain ⟨-, a, ha, b, hb, hab⟩ := delta_Iio D J hlJ i s hs
  refine ⟨heu.unit, a, b, ha, hb, ?_⟩
  have hrel : envRel D d p i = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) +
      (MvPolynomial.X i ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s) := by
    rw [envRel, Function.iterate_succ_apply', hi, step_eq]
  have hdiff : envRel D d p i - (MvPolynomial.C (heu.unit : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b)
      = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) + ((polyDelta D).δ s - (a * MvPolynomial.X i + b)) -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s := by
    rw [hrel, IsUnit.unit_spec]; ring
  rw [hdiff]
  exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (phi_mem D J hlJ he))) hab)
    (cc_mem_ideal _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ he)))

end GlobalTheory.EnvShape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinateStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_other_root_factors_action_first_coordinate : ∀ {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ} (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))) (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → (∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2)) → (∀ u, e ((X₀.map (toFr O)).mulVec u) = (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) → ∀ u, e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) = (0, fun c : Fin t => if (c : ℕ) = 0 then toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  first | exact @GlobalTheory.RootFactorProduct.prod_other_factors_action | exact GlobalTheory.RootFactorProduct.prod_other_factors_action | (intros; apply GlobalTheory.RootFactorProduct.prod_other_factors_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankEqOfActsThroughFirstBlockStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_eq_of_mulVec_through_first_block : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K) (ε : Matrix (Fin r) (Fin r) K), (∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) → F.rank = ε.rank := by
  first | exact @GlobalTheory.rank_eq_of_acts_through_first_block | exact GlobalTheory.rank_eq_of_acts_through_first_block | (intros; apply GlobalTheory.rank_eq_of_acts_through_first_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjectionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (E M : Matrix (Fin n) (Fin n) K) (d : Fin t → K), (∀ u, e (E.mulVec u) = (0, (e u).2)) → (∀ u, e (M.mulVec u) = (0, fun c => d c * (e u).2 c)) → E.rank = t ∧ blockPol E M = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  first | exact @GlobalTheory.CharBlock.rank_blockPol_proj | exact GlobalTheory.CharBlock.rank_blockPol_proj | (intros; apply GlobalTheory.CharBlock.rank_blockPol_proj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfCover
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.ClassPet

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cong_mul {N : ℕ} {a b : GAf L n} (ha : NG.Cong L n N a) (hb : NG.Cong L n N b) :
    NG.Cong L n N (a * b) := by
  refine ⟨Subgroup.mul_mem _ ha.1 hb.1, fun i j => ?_⟩
  choose y hy e using ha.2
  choose z hz e' using hb.2
  have hbU : ∀ k l, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := hb.1
  refine ⟨∑ k, y i k * (b.1 : Matrix (Fin n) (Fin n) (AL L)) k j + z i j,
    Subring.add_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hbU k j)) (hz i j), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hB : (b.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of z := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e']; ring
  have : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) = (a.1 : Matrix _ _ _) * (b.1 : Matrix _ _ _) := rfl
  rw [this]
  conv_lhs => rw [hA, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [hB]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem cong_one (N : ℕ) : NG.Cong L n N (1 : GAf L n) := by
  refine ⟨Subgroup.one_mem _, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩
  simp

theorem cong_inv {N : ℕ} {a : GAf L n} (ha : NG.Cong L n N a) : NG.Cong L n N a⁻¹ := by
  refine ⟨Subgroup.inv_mem _ ha.1, fun i j => ?_⟩
  choose y hy e using ha.2
  have hiU : ∀ k l, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := Subgroup.inv_mem _ ha.1
  refine ⟨-(∑ k, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * y k j),
    Subring.neg_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hiU i k) (hy k j)), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hinv : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix _ _ _) = 1 := by
    have : (a⁻¹ * a).1 = 1 := by simp
    exact congrArg (fun u : GL (Fin n) (AL L) => (u : Matrix (Fin n) (Fin n) (AL L))) this
  have key : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      -((N : AL L) • (((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * Matrix.of y)) := by
    calc ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1
        = ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - ((a⁻¹).1 : Matrix _ _ _) * (a.1 : Matrix _ _ _) := by rw [hinv]
      _ = _ := by rw [hA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]; abel
  have := congrFun (congrFun key i) j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul] at this
  rw [this]; ring

variable (L n) in

def congSub (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | NG.Cong L n N κ}
  mul_mem' := cong_mul
  one_mem' := cong_one N
  inv_mem' := cong_inv

theorem mem_congSub {N : ℕ} {κ : GAf L n} : κ ∈ congSub L n N ↔ NG.Cong L n N κ := Iff.rfl

theorem congSub_le_umax (N : ℕ) : congSub L n N ≤ Umax L n := fun _ h => h.1

theorem congSub_mul_le (N M : ℕ) : congSub L n (N * M) ≤ congSub L n N := fun _ h => NG.Cong.of_mul_left L n h

end GlobalTheory.ClassPet

namespace GlobalTheory.ClassPet

section Grp
variable {G : Type*} [Group G]

theorem relIndex_ne_zero_of_cover {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H)
    (hle : H ≤ K) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    let φ : F → K ⧸ H.subgroupOf K := fun f =>
      if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)
    refine Finite.of_surjective φ (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H κ =>
      obtain ⟨f, hf, hfκ⟩ := hF κ κ.2
      have hfK : f ∈ K := by
        have := K.mul_mem κ.2 (K.inv_mem (hle hfκ))
        simpa using this
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [φ, dif_pos hfK]
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem exists_cosetReps {H K : Subgroup G} (hle : H ≤ K) (hne : H.relIndex K ≠ 0) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ K) ∧ (∀ κ ∈ K, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H) ∧ F.card = H.relIndex K := by
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let o : K ⧸ H.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have ho : Function.Injective o := by
    intro q q' h
    have : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (Quotient.out q).2
  · intro κ hκ
    refine ⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))
      simpa [Subgroup.mem_subgroupOf, o] using h
    · rintro u ⟨hu, hu'⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have : q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K) := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')
      rw [this]
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ]
    show _ = (H.subgroupOf K).index
    rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem norm_eq_one_of_relIndex {J K : Subgroup G} (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (χ : J →* ℂˣ)
    (hχ : ∀ κ (h : κ ∈ K), χ ⟨κ, hle h⟩ = 1) (κ : J) : ‖((χ κ : ℂˣ) : ℂ)‖ = 1 := by
  haveI : (K.subgroupOf J).FiniteIndex := ⟨hne⟩
  obtain ⟨i, j, hij, e⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => ((κ ^ i : J) : J ⧸ K.subgroupOf J))
  have hmem : ((κ ^ i)⁻¹ * κ ^ j : J) ∈ K.subgroupOf J := QuotientGroup.eq.1 e
  have h1 : χ ((κ ^ i)⁻¹ * κ ^ j) = 1 := by
    have := hχ _ (Subgroup.mem_subgroupOf.1 hmem)
    rwa [Subtype.coe_eta] at this
  have h2 : ((χ κ : ℂˣ) : ℂ) ^ i = ((χ κ : ℂˣ) : ℂ) ^ j := by
    rw [map_mul, map_inv, map_pow, map_pow, inv_mul_eq_one] at h1
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h1
    simpa using this
  have h3 : ‖((χ κ : ℂˣ) : ℂ)‖ ^ i = ‖((χ κ : ℂˣ) : ℂ)‖ ^ j := by rw [← norm_pow, ← norm_pow, h2]
  have hpos : 0 < ‖((χ κ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  by_contra hne1
  exact hij (pow_right_injective₀ hpos hne1 h3)

end Grp

section Sum
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
  (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))

theorem classSum_add_left (f₁ f₂ f' : GAf L n → a.W) :
    classSum a β J T (f₁ + f₂) f' = classSum a β J T f₁ f' + classSum a β J T f₂ f' := by
  simp only [classSum, Pi.add_apply, LinearMap.map_add₂, mul_add, Finset.sum_add_distrib]

theorem classSum_smul_left (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T (c • f) f' = starRingEnd ℂ c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_add_right (f f₁ f₂ : GAf L n → a.W) :
    classSum a β J T f (f₁ + f₂) = classSum a β J T f f₁ + classSum a β J T f f₂ := by
  simp only [classSum, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem classSum_smul_right (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T f (c • f') = c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_conj (hβ : IsInvForm a β) (f f' : GAf L n → a.W) :
    classSum a β J T f' f = starRingEnd ℂ (classSum a β J T f f') := by
  simp only [classSum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hβ.1 (f' t) (f t)]

end Sum

end GlobalTheory.ClassPet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponents
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel.OddBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem residual_bound_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → ResBound bkP i s) → ResidualBoundOddPrimes bkP := by
  intro D N X bkP hAB hCh hRB i hl T hT
  obtain ⟨R, hR⟩ := hCh i T hT
  refine ⟨R, 4 * D.R.r * R, 4 * D.R.r * R + 2, fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hlt : 4 * D.R.r * R + 2 < X.l i ^ M := lt_of_le_of_lt hM (Nat.lt_pow_self hp.one_lt)
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, -⟩ := GlobalTheory.T.exists_open_normal_subgroup_under_inertia D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A R h
    (fun a => ⟨hLH (hh a), hLζ _ (hh a)⟩)
  choose φ g hφ hg using hFr
  have mono : ∀ V : Subgroup (GE N), U ⊓ H' ≤ V → Steps X i M V z P (fun q => d (P q)) := fun V hV =>
    ⟨fun a σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hV hg, hSt.2⟩
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  refine ⟨P, hAux, mono H' inf_le_right, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hPos : Position i s M P (fun q => d (P q)) φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) := by
    refine ⟨⟨fun q v hv => ?_, hAux.2⟩, ⟨z, L, hz, hLs s hs, mono L hUL'⟩, fun a => ⟨fun k hk => ?_, hφ a, hcj a⟩⟩
    · obtain ⟨h1, h2, h3, h4, -, h6⟩ := hAux.1 q v hv
      exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩
    · exact (hLs s hs).2.2.2.2 k (dec_le_of_frob_mem (N.plOm.2 _) (hφ a) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL a) hk)
  have hc := hco φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) (fun a => ⟨hcj a, g a, (hg a).1⟩) s hs
  rw [if_pos hl] at hc
  obtain ⟨m, hm, hu⟩ := (hRB i s (hT s hs) M R P _ φ _ Q hlt hPos hQ a Φ hΦ).1 hc F hF
  exact ⟨m, hm, (IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu).le⟩

end GlobalTheory.ResSel.OddBound
end

