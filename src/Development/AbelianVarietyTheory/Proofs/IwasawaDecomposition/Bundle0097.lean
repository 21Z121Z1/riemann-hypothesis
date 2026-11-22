import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusEigenFilEqQlMulTPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (r : ℕ) (x : Per.Acris l), phiA l x = (l : Per.Acris l) ^ r * x → C.j x ∈ Per.FilP l r → ∃ (z : ℤ_[l]) (k : ℕ), (l : Per.Acris l) ^ k * x = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) * C.t ^ r := by
  first | exact @GlobalTheory.MemLoc.fix_pow | exact GlobalTheory.MemLoc.fix_pow | (intros; apply GlobalTheory.MemLoc.fix_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExtStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdR_galois_invariants_eq_finExt : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.BdR l), (∀ g ∈ GK K, Per.σD g b = b) → ∃ y ∈ K.1, algebraMap (Per.BdRp l) (Per.BdR l) (C.o y) = b := by
  first | exact @GlobalTheory.MemLoc.InvDR.invariants_BdR | exact GlobalTheory.MemLoc.InvDR.invariants_BdR | (intros; apply GlobalTheory.MemLoc.InvDR.invariants_BdR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
section
namespace GlobalTheory.AnalyticNormality

open IsLocalRing

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  have hnoeth := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian
  have hquot := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv
  have hengine := GlobalTheory.T.associated_prime_localization_dvr
  have hclosed := GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
  have hdom := GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local
  have hred := GlobalTheory.T.adic_completion_reduced_of_jacobson
  have hcond := GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType
  intro A _ _ _ _ _ _
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  set m := maximalIdeal A with hm
  let R := AdicCompletion m A
  haveI : IsNoetherianRing R := hnoeth A m
  haveI : Module.Flat A R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsReduced R := hred A m (IsLocalRing.maximalIdeal_le_jacobson _)
  obtain ⟨x, hx0, hx⟩ := hcond A
  have hxR : algebraMap A R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular A x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap A R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hredq : ∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R)) := by
    intro q hq _
    obtain ⟨e⟩ := hquot A m q
    haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType A (A ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (A ⧸ q)
      haveI : IsScalarTower ℤ A (A ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ A (A ⧸ q)
    have hj : m.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ q)) := by
      haveI : IsLocalRing (A ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      refine Ideal.mem_comap.mpr (IsLocalRing.maximalIdeal_le_jacobson _ ?_)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ q)ˣ).1
      have h1 : Ideal.Quotient.mk q (a * b) = 1 := by
        rw [map_mul, hb]; exact hu.mul_val_inv
      have h2 : a * b - 1 ∈ q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : a * b - 1 ∈ m := IsLocalRing.le_maximalIdeal hq.ne_top h2
      have h4 : (1 : A) ∈ m := by
        have := m.sub_mem (m.mul_mem_right b ha) h3
        simpa using this
      exact (Ideal.ne_top_iff_one m).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h4
    haveI := hred (A ⧸ q) _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  have hcl : IsIntegrallyClosed R := by
    refine hclosed R (algebraMap A R x) hxR ?_ hx
    intro P _ hP
    obtain ⟨h1, h2⟩ := hengine A R x hx0 hredq P hP
    exact ⟨h1, inferInstance⟩
  exact ⟨hdom R hcl, hcl⟩

end GlobalTheory.AnalyticNormality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.InfTypeLocal

theorem denseRange_atInf (L : Type) [Field L] [NumberField L] :
    DenseRange (fun (k : Lˣ) (w : InfinitePlace L) => atInf w k) := by
  have hg : Topology.IsOpenEmbedding
      (Pi.map (fun (w : InfinitePlace L) => (Units.val : (w.Completion)ˣ → w.Completion))) :=
    Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have h1 := congrFun hk w
    rw [map_zero] at h1
    exact (v w).ne_zero h1
  refine ⟨v, hv, Units.mk0 k hk0, ?_⟩
  funext w
  exact Units.ext (congrFun hk w).symm

theorem continuous_infIdele (L : Type) [Field L] [NumberField L] (w : InfinitePlace L) :
    Continuous (infIdele L w) := by
  classical
  refine Continuous.units_map _ ?_
  exact Continuous.prodMk (continuous_mulSingle w) continuous_const

theorem exists_ext {L : Type} [Field L] (φ : L →+* ℂ) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧
      ∀ k : L, e (algebraMap L _ k) = φ k := by
  have h0 : ∀ k : L, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap L _ k) =
      (InfinitePlace.mk φ).embedding k := fun k =>
    InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun k => by rw [h0, h]⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp hc, fun k => ?_⟩
    rw [RingHom.comp_apply, h0, h]
    simp

open Classical in

theorem infType_iff_local : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ n : I → ℤ, ((∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ↔ ∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) := by
  intro L _ _ I _ φ hφ ψ hψ n
  have hd : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) := by
    intro k
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    rfl
  constructor
  · intro h
    choose e hec he using fun i => exists_ext (φ i)
    have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => ∏ w, ((ψ (infIdele L w (u w)) : ℂˣ) : ℂ)) =
        fun u => ∏ i, (e i (u (InfinitePlace.mk (φ i))) / ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ)) ^ n i := by
      refine (denseRange_atInf L).equalizer ?_ ?_ ?_
      · refine continuous_finsetProd _ fun w _ => ?_
        exact Units.continuous_val.comp (hψ.comp ((continuous_infIdele L w).comp (continuous_apply w)))
      · refine continuous_finsetProd _ fun i _ => ?_
        have h1 : Continuous fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => e i (u (InfinitePlace.mk (φ i))) :=
          (hec i).comp (Units.continuous_val.comp (continuous_apply _))
        have h2 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, e i (u (InfinitePlace.mk (φ i))) ≠ 0 := fun u =>
          (map_ne_zero _).2 (Units.ne_zero (u (InfinitePlace.mk (φ i))))
        have h3 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ) ≠ 0 := fun u => by
          exact_mod_cast norm_ne_zero_iff.2 (h2 u)
        exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _ fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
      · funext k
        show ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
          ∏ i, (e i (algebraMap L _ (k : L)) / ((‖e i (algebraMap L _ (k : L))‖ : ℝ) : ℂ)) ^ n i
        rw [← hd, h]
        simp only [he]
    intro i k
    have h1 := congrFun key (Pi.mulSingle (InfinitePlace.mk (φ i)) (atInf _ k))
    beta_reduce at h1
    rw [Finset.prod_eq_single (InfinitePlace.mk (φ i)), Finset.prod_eq_single i] at h1
    · rw [Pi.mulSingle_eq_same] at h1
      rw [h1, ← he i k]
      rfl
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne (fun hh => hj (hφ.1 hh))]
      simp
    · simp
    · intro w _ hw
      rw [Pi.mulSingle_eq_of_ne hw]
      simp
    · simp
  · intro h k
    rw [hd, ← hφ.prod_comp]
    exact Finset.prod_congr rfl fun i _ => h i k

end GlobalTheory.InfTypeLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLogTheta

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem eigen_add (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c d : G → R) (t : R) (ht : t ≠ 0)
    (hθt : θ t = 0) (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * (y + d g * t ^ (n + 1))) →
      ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w + d g * t := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow, map_add, map_mul, map_pow, hθt,
        zero_pow (Nat.succ_ne_zero _), mul_zero, add_zero]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem core_form (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.BdR l) (d : GQ l → Per.BdRp l)
    (hb : ∀ g : GQ l, Per.σD g b = b + algebraMap (Per.BdRp l) (Per.BdR l) (d g * C.j C.t)) :
    ∃ (a : ℚ_[l]) (v : Per.BdRp l), b = algebraMap (Per.BdRp l) (Per.BdR l)
      (C.o (algebraMap ℚ_[l] (Om l) a) + C.j C.t * v) := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C
  have htate := GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension l C (botExt l)
  have hast := GlobalTheory.T.cLTate_invariants_finiteExtension_mem l (botExt l)
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  let c : GQ l → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : GQ l, Per.σDp g t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, InvDR.j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hθt : Per.θD l t = 0 := (hker t).2 ht1
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : GQ l, Per.σC g x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g _ => by simpa only [hθc] using h g
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : GQ l, Per.σDp g y = c g ^ n * (y + d g * t ^ (n + 1)) := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g]
    simp only [map_mul, map_pow, map_add]
    rw [← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_add (Per.θD l) (fun g : GQ l => Per.σDp g) (fun g => Per.σC g) c d t ht0
    hθt hker' hc (fun g y => hθ g y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g _ => by
    rw [← hθ, hw' g, map_add, map_mul, hθt, mul_zero, add_zero]
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hk
  obtain ⟨v, hv⟩ := hker' (w - C.o (algebraMap ℚ_[l] (Om l) a))
    (by rw [map_sub, C.o_sec.th, hkθ, sub_self])
  refine ⟨a, v, ?_⟩
  rw [← hv, add_sub_cancel]
  have : IsDomain (Per.BdR l) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (b : P.R.B) (c : GQ l → ℚ_[l]), (∀ g : GQ l, P.actQ g b - b = c g • P.tB) →
    ∃ a : ℚ_[l], P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P) ∈ (P.PD (botExt l)).Fil 0 := by
  intro l _ P AI T b c hb
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have hι : ∀ g : GQ l, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun g => by
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at this
    exact this.symm
  have ht : T.eD (P.ιB P.tB) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) := by
    rw [hC.ι, hC.t, Core.tB, C.ι_j]
  have hq : ∀ a : ℚ_[l], T.eD (P.ιB (algebraMap ℚ_[l] P.R.B a)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (algebraMap ℚ_[l] (Om l) a)) := fun a => by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hC.o]
    rfl
  obtain ⟨a, v, h⟩ := core_form l C (T.eD (P.ιB b)) (fun g => C.o (algebraMap ℚ_[l] (Om l) (c g))) fun g => by
    rw [← T.actD, hι, map_mul, ← hq, ← ht, ← map_mul, ← map_mul, ← map_add, ← map_add, ← Algebra.smul_def,
      ← hb, add_sub_cancel]
  refine ⟨a, ?_⟩
  have h1 : T.eD (P.ιB (tInv P)) * algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) = 1 := by
    rw [← ht, ← map_mul, ← map_mul, tInv_mul, map_one, map_one]
  have h2 : T.eD (P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P)) =
      algebraMap (Per.BdRp l) (Per.BdR l) v := by
    rw [map_mul, map_mul, map_sub, map_sub, hq, h, map_add, map_mul]
    linear_combination algebraMap (Per.BdRp l) (Per.BdR l) v * h1
  rw [T.fil, h2]
  have h3 : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
    have := (T.fil (botExt l) 0 1).1 (P.PD (botExt l)).one_mem
    rwa [map_one] at this
  have h4 := (Per.FilD l 0).smul_mem v h3
  rwa [Algebra.smul_def, mul_one] at h4

end GlobalTheory.Pst.NoLogTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValues
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BaseChars

theorem exists_chars_zmod {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {z : K} (hz : IsPrimitiveRoot z (p * (p - 1))) :
    ∃ (ψ : AddChar (ZMod p) K) (om : (ZMod p)ˣ →* Kˣ), ψ 1 ≠ 1 ∧ Function.Injective om := by
  haveI := Fact.mk hp
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have hpos : 0 < p * (p - 1) := Nat.mul_pos hp.pos hp1
  have h1 : IsPrimitiveRoot (z ^ (p - 1)) p := hz.pow hpos (mul_comm _ _)
  have h2 : IsPrimitiveRoot (z ^ p) (p - 1) := hz.pow hpos rfl
  obtain ⟨u, hu⟩ := h2.isUnit hp1.ne'
  have h3 : IsPrimitiveRoot u (p - 1) := IsPrimitiveRoot.coe_units_iff.1 (hu ▸ h2)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hou : orderOf u = p - 1 := h3.eq_orderOf.symm
  refine ⟨AddChar.zmodChar p h1.pow_eq_one, monoidHomOfForallMemZpowers hg (g' := u) (by rw [hog, hou]), ?_, ?_⟩
  · rw [AddChar.zmodChar_apply, ZMod.val_one, pow_one]
    exact h1.ne_one hp.one_lt
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    rw [map_zpow, monoidHomOfForallMemZpowers_apply_gen, ← orderOf_dvd_iff_zpow_eq_one, hou, ← hog] at hx
    exact orderOf_dvd_iff_zpow_eq_one.1 hx

theorem eq_of_pow_eq {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {om : (ZMod p)ˣ →* Kˣ} (hom : Function.Injective om)
    {a b : ℕ} (ha : a < p - 1) (hb : b < p - 1) (h : ∀ x, om x ^ a = om x ^ b) : a = b := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h1 := h g
  rw [← map_pow, ← map_pow] at h1
  exact pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)

theorem nonempty_equiv_zmod {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hw : Ideal.absNorm w.asIdeal = p) : Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod p) := by
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  exact ⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩

theorem exists_chars_of_roots {X : Fields} (Pr : Primes X) (hPr : Pr.Ok) (m : ℕ) (hm : ∀ i, 2 * m < Pr.g i - 1)
    (hz : ∀ i, ∃ z : X.K, IsPrimitiveRoot z (Pr.g i * (Pr.g i - 1)))
    (mu : Fin m → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (eta : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) :
    ∃ Ch : Chars X Pr m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  classical
  have h0 : ∀ i, ∃ (ψ : AddChar (ZMod (Pr.g i)) X.K) (om : (ZMod (Pr.g i))ˣ →* X.Kˣ),
      ψ 1 ≠ 1 ∧ Function.Injective om := fun i => by
    obtain ⟨z, hz⟩ := hz i
    exact exists_chars_zmod (hPr.g_prime i) hz
  choose ψ om hψ hom using h0
  have hmem : ∀ w : {w // w ∈ Pr.vGs}, ∃ i, w.1 ∈ Pr.vG i := fun w => by
    have h := w.2
    unfold Primes.vGs at h
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hg : Function.Injective Pr.g := by
    intro i j hij
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all
  have h1 : ∀ w : {w // w ∈ Pr.vGs}, ∃ (ψw : AddChar (𝓞 X.E ⧸ w.1.asIdeal) X.K)
      (omw : (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* X.Kˣ), ∀ i, w.1 ∈ Pr.vG i →
      ∃ φ : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* ZMod (Pr.g i), (∀ x, ψw x = ψ i (φ x)) ∧
        ∀ (x : (𝓞 X.E ⧸ w.1.asIdeal)ˣ) (a : (ZMod (Pr.g i))ˣ), φ x = a → omw x = om i a := fun w => by
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ⟩ := nonempty_equiv_zmod (hPr.g_prime i) w.1 (hPr.vG_norm i w.1 hi)
    refine ⟨(ψ i).compAddMonoidHom φ.toAddMonoidHom, (om i).comp (Units.map φ.toMonoidHom), fun i' hi' => ?_⟩
    obtain rfl : i = i' := hg ((hPr.vG_norm i w.1 hi).symm.trans (hPr.vG_norm i' w.1 hi'))
    refine ⟨φ, fun x => rfl, fun x a h => ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    exact Units.ext h
  choose ψw omw hw using h1
  refine ⟨⟨ψw, fun j w => omw w ^ (2 * (j.1 + 1)), mu, eta⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro w h
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ, h1, -⟩ := hw w i hi
    apply hψ i
    rw [← map_one φ, ← h1]
    exact DFunLike.congr_fun h 1
  · intro w j j' h
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ, -, h2⟩ := hw w i hi
    have hj := j.2
    have hj' := j'.2
    have hmi := hm i
    have h3 : 2 * (j.1 + 1) = 2 * (j'.1 + 1) := by
      refine eq_of_pow_eq (hPr.g_prime i) (hom i) (by omega) (by omega) fun a => ?_
      rw [← h2 (Units.map φ.symm.toMonoidHom a) a (φ.apply_symm_apply _)]
      exact DFunLike.congr_fun h _
    exact Fin.ext (by omega)
  · intro i w w' hi hi' j a x x' hx hx'
    obtain ⟨φ, -, h2⟩ := hw w i hi
    obtain ⟨φ', -, h2'⟩ := hw w' i hi'
    show omw w x ^ _ = omw w' x' ^ _
    rw [h2 x (Units.map φ.toMonoidHom x) rfl, h2' x' (Units.map φ.toMonoidHom x)]
    show φ' x' = φ x
    rw [hx, hx', map_intCast, map_intCast]
  · intro i w w' hi hi' a
    obtain ⟨φ, h1, -⟩ := hw w i hi
    obtain ⟨φ', h1', -⟩ := hw w' i hi'
    show ψw w _ = ψw w' _
    rw [h1, h1', map_intCast φ, map_intCast φ']
  · intro i
    refine ⟨om i, hom i, fun w hi j a x hx => ?_⟩
    haveI := Fact.mk (hPr.g_prime i)
    obtain ⟨φ, -, h2⟩ := hw w i hi
    show omw w x ^ _ = _
    rw [h2 x a (by rw [hx, map_natCast, ZMod.natCast_zmod_val])]

theorem exists_chars : ∀ (B : Base) (X : PreX B.toPre) (mu : Fin B.R.m → HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ)
    (eta : HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ),
    ∃ Ch : Chars B.fields (B.primes X) B.R.m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  intro B X mu eta
  refine exists_chars_of_roots (B.primes X) (GlobalTheory.BasePrimes.primes_ok B X).1 B.R.m (fun i => ?_) (fun i => ?_) mu eta
  · have h1 := (B.primes_sizes X).g_big i
    have h2 := B.R.m_add_three_le_k
    have h3 : 0 < B.fields.f := by
      rw [B.fields_f]
      unfold Ranks.f Ranks.n
      positivity
    refine lt_of_le_of_lt ?_ h1
    nlinarith
  · have hp := B.host.g_prime i
    obtain ⟨z, -, hz⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
    have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
    refine ⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩
    rw [hz]
    exact Complex.isPrimitiveRoot_exp _ hne

end GlobalTheory.BaseChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_generator_extend_dense_proOpen : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  first | exact @GlobalTheory.GenExtendDense.existsUnique_gen_extend | exact GlobalTheory.GenExtendDense.existsUnique_gen_extend | (intros; apply GlobalTheory.GenExtendDense.existsUnique_gen_extend <;> assumption)
end

