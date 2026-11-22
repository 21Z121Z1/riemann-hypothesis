import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpDerEigenIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

def expDer (he : IsExp y e) (w : Fin g → ℂ) : epsPt y ⟶ G := (he.2.2.2.1 w).exists.choose

variable (he : IsExp y e)
include he

theorem expDer_spec (w : Fin g → ℂ) : IsDerivAt0 (fun z => (e z).left) w (expDer he w).left :=
  (he.2.2.2.1 w).exists.choose_spec

theorem exp_zero : e 0 = 1 := by
  have h := he.1 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_eq_iff (w : Fin g → ℂ) (v : epsPt y ⟶ G) :
    IsDerivAt0 (fun z => (e z).left) w v.left ↔ expDer he w = v :=
  ⟨fun hv => Over.OverMorphism.ext
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he w) hv), fun hv => hv ▸ expDer_spec he w⟩

theorem expDer_base (w : Fin g → ℂ) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (1 : Over.mk y ⟶ G).left := by
  rw [(expDer_spec he w).1]; show (e 0).left = _; rw [exp_zero he]

theorem expDer_injective : Function.Injective (expDer he) := by
  intro w w' h
  have h1 := expDer_spec he w
  have h2 := expDer_spec he w'
  rw [← h] at h2
  have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (e 0).left := h1.1
  exact (he.2.2.2.2 _ hb).unique h1 h2

theorem expDer_surj (v : epsPt y ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left) :
    ∃ w, expDer he w = v := by
  obtain ⟨w, hw, -⟩ := he.2.2.2.2 v (by rw [hv, exp_zero he])
  exact ⟨w, (expDer_eq_iff he w v).1 hw⟩

theorem expDer_add (w w' : Fin g → ℂ) : expDer he (w + w') = expDer he w * expDer he w' :=
  (expDer_eq_iff he _ _).1 (GlobalTheory.UnifCompare.isDerivAt0_mul (by rw [exp_zero he]) (expDer_spec he w)
    (expDer_spec he w'))

theorem expDer_zero : expDer he 0 = 1 := by
  have h := expDer_add he 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_smul (c : ℂ) (w : Fin g → ℂ) :
    (expDer he (c • w)).left = spMap (epsScale c) ≫ (expDer he w).left :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he _)
    (GlobalTheory.UnifCompare.isDerivAt0_smul (expDer_spec he w) c)

theorem expDer_prod {n : ℕ} (f : Fin n → Fin g → ℂ) :
    (List.ofFn fun j => expDer he (f j)).prod = expDer he (∑ j, f j) := by
  induction n with
  | zero => simp [expDer_zero he]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => f j.succ), Fin.sum_univ_succ, expDer_add he]

theorem expDer_mulVec (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (w : Fin g → ℂ) : expDer he (M *ᵥ w) = expDer he w ≫ φ := by
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (expDer_spec he w) φ.left
  have h2 : (fun z => (e z).left ≫ φ.left) = fun z => (e (Matrix.mulVecLin M z)).left := by
    funext z; rw [Matrix.mulVecLin_apply, hM z, Over.comp_left]
  rw [h2, GlobalTheory.ThetaWitness.isDerivAt0_comp_linear_iff (fun z => (e z).left) he.2.2.1] at h1
  exact (expDer_eq_iff he _ _).1 h1

theorem expDer_eigen_iff (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (c : ℂ) (w : Fin g → ℂ) :
    (expDer he w ≫ φ).left = spMap (epsScale c) ≫ (expDer he w).left ↔ M *ᵥ w = c • w := by
  rw [← expDer_mulVec he M φ hM, ← expDer_smul he]
  constructor
  · intro h
    exact expDer_injective he (Over.OverMorphism.ext h)
  · intro h
    rw [h]

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.MidBlock

section Alg

variable {A A' : Type} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A']

theorem qdet_map (φ : A →ₐ[ℂ] A') {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, map_add]
  split_ifs <;> simp

theorem qdet_mem (S : Subalgebra ℂ A) {n : ℕ} {E : Fin n → Fin n → A} (h : ∀ a b, E a b ∈ S) (u : ℂ) :
    Formalism.REAL.qdet E u ∈ S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem comm_qdet {n : ℕ} {E : Fin n → Fin n → A} {z : A} (h : ∀ a b, Commute z (E a b)) (u : ℂ) :
    Commute z (Formalism.REAL.qdet E u) := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Formalism.REAL.Tm
  exact Commute.add_right (GlobalTheory.CapHC.ite_algebraMap_comm _ _ _).symm (h _ _)

theorem qdet_one (E : Fin 1 → Fin 1 → A) (u : ℂ) : Formalism.REAL.qdet E u = algebraMap ℂ A u + E 0 0 := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  simp

theorem glComm {n : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {a b c d : Fin n} (hbc : b ≠ c)
    (hda : d ≠ a) : Commute (X a b) (X c d) := by
  have h := hX a b c d
  rw [if_neg hbc, if_neg hda, sub_zero] at h
  exact sub_eq_zero.1 h

end Alg

section Stab

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ N, f x ∈ N}
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  add_mem' := fun ha hb x hx => N.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := fun c x hx => by simpa [Module.algebraMap_end_apply] using N.smul_mem c hx

theorem mem_stab {N : Submodule ℂ M} {f : Module.End ℂ M} : f ∈ stab N ↔ ∀ x ∈ N, f x ∈ N := Iff.rfl

theorem upperSpan_maps {N K : Submodule ℂ M} {r m : ℕ} (Y : Fin (r + m) → Fin (r + m) → stab N)
    (hY : ∀ p q, ∀ x ∈ N, (Y (Fin.castAdd m p) (Fin.natAdd r q) : Module.End ℂ M) x ∈ K)
    {y : stab N} (hy : y ∈ GlobalTheory.CapHC.upperSpan Y) : ∀ x ∈ N, (y : Module.End ℂ M) x ∈ K := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, rfl⟩ := hy
    intro x hx
    exact hY p q _ (mem_stab.1 w.2 x hx)
  | zero => intro x _; simp
  | add a b _ _ ha hb => intro x hx; simpa using K.add_mem (ha x hx) (hb x hx)
  | smul c a _ ha => intro x hx; simpa using K.smul_mem c (ha x hx)

end Stab

section Main

theorem blk_castAdd_lt {n₁ : ℕ} (p : Fin (1 + n₁)) (q : Fin 1) :
    blk n₁ (Fin.castAdd 1 p) < blk n₁ (Fin.natAdd (1 + n₁) q) := by
  rw [blk_y]
  refine Fin.addCases (fun a => ?_) (fun k => ?_) p <;> simp [blk]

end Main

end GlobalTheory.LeviHC.MidBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandGeneratorMemQuantumDet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.CapelliGelfand

open Formalism.REAL Finset

theorem epow_eq_pow {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp [epow, pow_succ, Matrix.mul_apply, ih]

theorem etr_succ_eq_gelfA {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (k : ℕ) :
    etr E (k + 1) = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]; simp [etr, epow_eq_pow]

theorem etr_mem_adjoin_qdet (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (N : ℕ) : etr X N ∈ Algebra.adjoin ℂ (Set.range (qdet X)) := by
  set S := Algebra.adjoin ℂ (Set.range (qdet X)) with hS
  have hq : ∀ u, qdet X u ∈ S := fun u => Algebra.subset_adjoin ⟨u, rfl⟩
  cases n with
  | zero => simp [etr]
  | succ m =>
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet A (m + 1) X
      have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
          qminor X (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
        intro i j
        obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m X (Fin.succAbove j) (Fin.succAbove i) 0
        exact ⟨c', fun w => by simpa using hc' w⟩
      choose cm hcm using hmin
      let Rs : ℂ → A := fun w => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor X (Fin.succAbove j) (Fin.succAbove i) w
          * epow X (N + 1) j i
      let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow X (N + 1) j i
      have hR : ∀ w : ℂ, Rs w = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
        intro w
        simp only [Rs, Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
        conv_lhs => enter [2, x]; rw [sum_comm]
        rw [sum_comm]
      let f : ℂ → A := fun u => qdet X u * etr X N - Rs u
      let a : ℕ → A := fun i => c i * etr X N - if i < m + 1 then Rc i else 0
      have hf : ∀ u, f u = ∑ i ∈ range (m + 1 + 1), u ^ i • a i := by
        intro u
        simp only [f, a, hc u, hR u, sum_mul, smul_mul_assoc, smul_sub, sum_sub_distrib]
        congr 1
        rw [sum_range_succ _ (m + 1), if_neg (lt_irrefl _), smul_zero, add_zero]
        exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.mp hi)]
      have hmem : ∀ u, f u ∈ S := by
        intro u
        have h1 := GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m X hX u N
        rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add] at h1
        have key : algebraMap ℂ A ((-1) ^ N) * f u = algebraMap ℂ A ((u - m) ^ (N + 1)) * (qdet X (u + 1) - qdet X u)
            - qdet X u * ∑ k ∈ range N, algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr X k := by
          simp only [f]
          rw [mul_sub, ← mul_assoc, Algebra.commutes, mul_assoc, sub_eq_sub_iff_add_eq_add, h1]
          abel
        have hm : algebraMap ℂ A ((-1) ^ N) * f u ∈ S := by
          rw [key]
          refine sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (hq _) (hq _)))
            (mul_mem (hq _) (sum_mem fun k hk => mul_mem (Subalgebra.algebraMap_mem _ _) (ih k (mem_range.mp hk))))
        have : f u = algebraMap ℂ A ((-1) ^ N) * (algebraMap ℂ A ((-1) ^ N) * f u) := by
          rw [← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one, one_mul]
        rw [this]
        exact mul_mem (Subalgebra.algebraMap_mem _ _) hm
      have htop := GlobalTheory.LeviHC.coeff_mem_span hf (i := m + 1) (Nat.lt_succ_self _)
      have ha : a (m + 1) = etr X N := by simp [a, hc1]
      rw [ha] at htop
      have hle : Submodule.span ℂ (Set.range f) ≤ Subalgebra.toSubmodule S :=
        Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact hmem u)
      exact hle htop

theorem gelfA_mem_adjoin_qdet : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
    ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X)) := by
  intro A _ _ n X hX k
  rw [← etr_succ_eq_gelfA]
  exact etr_mem_adjoin_qdet A n X hX (k + 1)

end GlobalTheory.CapelliGelfand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotMemSupportCokernelOfNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.VB

theorem genericPoint_notMem_support_cokernel_of_ne_zero :
    ∀ (X : Scheme.{0}) [IsIntegral X] (E L : X.Modules) (φ : E ⟶ L), IsVB L 1 → φ ≠ 0 → genericPoint X ∉ GlobalTheory.QCoh.support (Limits.cokernel φ) := by
  intro X _ E L φ hL h0
  have hex : ∃ (V : X.Opens) (s : Γ(E, V)), φ.app V s ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h0
    ext V s
    exact (hc V s).trans rfl
  obtain ⟨V, s, hs⟩ := hex
  have hV : genericPoint X ∈ V := by
    by_contra hη
    refine hs (QCoh.section_eq_zero_of_germ _ fun x hx => ?_)
    exact absurd (VB.genericPoint_mem hx) hη
  have hg : L.presheaf.germ V _ hV (φ.app V s) ≠ 0 := fun h => hs (hL.isTorsionFree V hV _ h)
  have hr : Module.finrank X.functionField (genStalk L) = 1 := hL.genRank_eq
  have hsurj : Function.Surjective (QCoh.stalkLinear φ (genericPoint X)) := by
    intro w
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hg).1 hr w
    refine ⟨c • E.presheaf.germ V _ hV s, ?_⟩
    rw [map_smul, QCoh.stalkLinear_germ]
    exact hc
  have hexact := (QCoh.exact_iff_stalkLinear _).1 (ShortComplex.exact_cokernel φ) (genericPoint X)
  refine QCoh.notMem_support_iff.2 ⟨fun a b => ?_⟩
  have key : ∀ y, y = (0 : ((Limits.cokernel φ).presheaf.stalk (genericPoint X) :)) := by
    intro y
    obtain ⟨t, rfl⟩ := QCoh.stalkLinear_surjective (Limits.cokernel.π φ) (genericPoint X) y
    obtain ⟨u, rfl⟩ := hsurj t
    exact (hexact _).2 ⟨u, rfl⟩
  rw [key a, key b]

end GlobalTheory.VB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedFirstIsometricDualO1
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ProjSpace GlobalTheory.QCoh

namespace GlobalTheory.TautFlag

theorem resM_s_eq_ratioOn_smul (j j' : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) (h' : V ≤ chart ℤ 1 j') :
    resM K h' (s j') = ratioOn V j' h' j • resM K h (s j) := by
  have hm : Mono (kernel.ι quotMap) := equalizer.ι_mono
  refine injective_app_of_mono (kernel.ι quotMap) V ?_
  refine Eq.trans ?_ (kernel_ι_app_smul_resM_s j h _).symm
  rw [ratioOn_mul_ratioOn, ratioOn_mul_ratioOn]
  exact (app_resM _ _ _).trans ((congrArg (resM E h') (map_s j')).trans (resM_v j' h'))

theorem val_detUnit_rankOne_of_eq_smul {X : Scheme.{0}} {F : X.Modules} {U U' V : X.Opens} {a : Fin 1 → Γ(F, U)}
    {a' : Fin 1 → Γ(F, U')} (ha : IsFrame a) (ha' : IsFrame a') (h : V ≤ U) (h' : V ≤ U') (c : Γ(X, V))
    (hc : resM F h' (a' 0) = c • resM F h (a 0)) : (ha.detUnit ha' h h' : Γ(X, V)) = c := by
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
    hc, ← ha.basis_apply h, map_smul, Module.Basis.repr_self]
  simp

theorem det_g_adapt₀ (j j' : Fin 2) :
    (VB.det (flag.gr 0) 1).g (adapt₀ j).quot (adapt₀ j').quot = ((O1 ℤ 1).g j j')⁻¹ := by
  refine Units.ext (val_detUnit_rankOne_of_eq_smul _ _ _ _ _ ?_)
  refine (app_resM (VMetric.stepSeq flag 0).g inf_le_right (s j')).symm.trans ?_
  refine (congrArg ((VMetric.stepSeq flag 0).g.app _) (resM_s_eq_ratioOn_smul j j' inf_le_left inf_le_right)).trans ?_
  exact (Scheme.Modules.Hom.app_smul _ _ _).trans
    (congrArg (_ • ·) (app_resM (VMetric.stepSeq flag 0).g inf_le_left (s j)))

theorem grLB_zero_φ (σ : ℤ →+* ℂ) (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    ((VMetric.grLB flag 0 stdH.cInf).φ σ).φ (adapt₀ j).quot y = -Real.log (nsqV j y).re := by
  have e := Met.quot_G ((stdH.h.stepMet flag 0).met σ) (VMetric.stepSeq_shortExact flag 0)
    (flag.isVB (Fin.castSucc 0)) (flag.isVB_gr 0) (adapt₀ j) hy
  refine congrArg (fun z : ℂ => -Real.log z.re) ((congrArg Matrix.det e).trans ((Matrix.det_fin_one _).trans ?_))
  refine Eq.trans ?_ (gram_adapt₀ j hy 0 0)
  have key (H : Matrix (Fin 0 ⊕ Fin 1) (Fin 0 ⊕ Fin 1) ℂ) : quotGram H 0 0 = H (.inr 0) (.inr 0) := by
    simp [quotGram, toBlocks₂₂]
  exact key _

theorem fubini_study_weight_eq_log_norm (σ : ℤ →+* ℂ) (j : Fin 2) (y : CxPts (PSpace.str ℤ 1) σ) :
    ((hermitianTwistingSheaf ℤ 1).φ σ).φ j y = Real.log (nsqV j y).re := by
  change (ProjAn.fsO1 ℤ σ 1).φ j y = _
  refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ ?_)
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Fin.sum_univ_two _).trans ?_
  simp only [nsqV, Complex.mul_conj, Complex.add_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rfl

theorem isometric_grLB_zero :
    (VMetric.grLB TautFlag.flag 0 TautFlag.stdH.cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual :=
  HermLB.Isometric.symm (HermLB.isometric_of_chart (L := (hermitianTwistingSheaf ℤ 1).dual) (fun j => (adapt₀ j).quot)
    (fun _ => le_rfl) (fun x j j' _ _ => congrArg (gm (𝟙 _) x _) (det_g_adapt₀ j j').symm)
    fun σ j y hy => (grLB_zero_φ σ j hy).trans (congrArg (- ·) (fubini_study_weight_eq_log_norm σ j y).symm))

end GlobalTheory.TautFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue GlobalTheory.CechPic
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)

namespace GlobalTheory

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
  {E E' : X.Modules} {r : ℕ}

theorem isometric_det_map {h : VMetric p E r} (H : h.IsCInf) (φ : E ≅ E') :
    (det H).Isometric (det (H.map φ)) :=
  HermLB.isometric_of_chart (L := det H) (M := det (H.map φ)) (fun c : Chart E r => c.map φ)
    (fun _ => le_rfl)
    (fun x c c' _ _ => congrArg (gm (𝟙 X) x _)
      (IsFrame.detUnit_map_iso c.isFrame c'.isFrame φ.hom _ _).symm)
    fun σ c _ hy => congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Real.log M.det.re)
      ((h.met σ).map_G φ c hy)

theorem isometric_det_pull {h : VMetric p E r} (H : h.IsCInf) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (det (H.pull π hπ)).Isometric ((det H).pull π hπ) := by
  have := h.isVB.isQuasicoherent
  refine HermLB.isometric_of_local (L := det (H.pull π hπ)) (M := (det H).pull π hπ)
    (fun c : Chart E r => π ⁻¹ᵁ c.U) (fun x => ?_) (fun c _ => c) (fun c => c.pull h.isVB π)
    (fun _ _ h => mem_pull.2 h) (fun _ => le_rfl) (fun _ => 1) (fun x c c' hc hc' => ?_)
    fun σ c y hy => ?_
  · exact exists_chart h.isVB.isLB_det (π x)
  · have e₁ := gm_pull_g (VB.det E r) π (𝟙 Y) x (fun _ => c) (fun _ => c') (mem_pull.2 hc)
      (mem_pull.2 hc')
    have e₂ := gm_pull (𝟙 Y) π x (c.U ⊓ c'.U) ⟨hc, hc'⟩ ((VB.det E r).g c c')
    have e₃ : (VB.det _ r).g (c.pull h.isVB π) (c'.pull h.isVB π) =
        pullU π (c.U ⊓ c'.U) ((VB.det E r).g c c') := by
      refine Units.ext ((IsFrame.val_detUnit_pullback c.isFrame c'.isFrame π inf_le_left
        inf_le_right (T := π ⁻¹ᵁ (c.U ⊓ c'.U)) le_rfl).trans ?_)
      rw [Scheme.Hom.appLE_eq_app]
      rfl
    have e₄ := e₁.trans (e₂.symm.trans (congrArg (gm (𝟙 Y) x _) e₃.symm))
    rw [map_one, map_one, mul_one]
    exact (mul_inv_eq_one.2 e₄).symm
  · rw [logSq_one hy, add_zero]
    refine (((det H).φ σ).pull_φ π hπ _ y).trans ?_
    exact congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Real.log M.det.re)
      ((h.met σ).pull_G π hπ c hy).symm

theorem quot_pullStep (fl : Vert.Flag E r) (π : Y ⟶ X) (i : Fin r)
    (a : AdaptedChart (stepSeq fl i) i 1) :
    (pullStep fl π i a).quot = (a.quot.pull (fl.isVB_gr i) π).map (fl.pullGrIso π i) := by
  have := (fl.isVB_gr i).isQuasicoherent
  have e : (pullStep fl π i a).quot.e =
      ((a.quot.pull (fl.isVB_gr i) π).map (fl.pullGrIso π i)).e := by
    funext j
    refine Eq.trans ?_ (congrArg ((fl.pullGrIso π i).hom.app _)
      (QCoh.pullback_map_app_pullbackSections π (fl.π i) le_rfl (a.t j)))
    exact (congr(($(fl.map_π_pullGrIso π i)).app _ _)).symm
  have key : ∀ {F : Y.Modules} {U : Y.Opens} {e e' : Fin 1 → Γ(F, U)} (he : IsFrame e)
      (he' : IsFrame e'), e = e' → (⟨U, e, he⟩ : Chart F 1) = ⟨U, e', he'⟩ := by
    rintro F U e e' he he' rfl
    rfl
  exact key _ _ e

theorem grMet_pull (h : VMetric p E r) (fl : Vert.Flag E r) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (i : Fin r) : (h.pull π hπ).grMet (fl.pull π) i =
      ((h.grMet fl i).pull π hπ).map (fl.pullGrIso π i) := by
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) (PtsOver.map π hπ _ z)
  have ha' : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U) := ha
  refine ⟨(pullStep fl π i a).quot, ha', ?_⟩
  refine ((((h.pull π hπ).stepMet (fl.pull π) i).met σ).quot_G (stepSeq_shortExact (fl.pull π) i)
    ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) (pullStep fl π i a) ha').trans ?_
  rw [gram_pullStep h hπ a ha', quot_pullStep]
  refine Eq.symm (((((h.grMet fl i).met σ).pull π hπ).map_G (fl.pullGrIso π i)
    (a.quot.pull (fl.isVB_gr i) π) ha').trans ?_)
  refine (((h.grMet fl i).met σ).pull_G π hπ a.quot ha).trans ?_
  exact ((h.stepMet fl i).met σ).quot_G (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) a ha

theorem isometric_grLB_pull (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r)
    (π : Y ⟶ X) (hπ : π ≫ p = q) (i : Fin r) :
    (VMetric.grLB (fl.pull π) i (H.pull π hπ)).Isometric ((VMetric.grLB fl i H).pull π hπ) := by
  have key : ∀ {F : Y.Modules} {h₁ h₂ : VMetric q F 1} (H₁ : h₁.IsCInf) (H₂ : h₂.IsCInf),
      h₁ = h₂ → det H₁ = det H₂ := by
    rintro F h₁ h₂ H₁ H₂ rfl
    rfl
  rw [grLB, key _ (((H.grMet fl i).pull π hπ).map (fl.pullGrIso π i)) (grMet_pull h fl π hπ i)]
  exact (isometric_det_map _ _).symm.trans (isometric_det_pull (H.grMet fl i) π hπ)

end VMetric

end GlobalTheory
end
end

