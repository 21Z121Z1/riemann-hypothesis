import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0249
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOneVectorStepCompatibleChangeOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchange
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.ExStruct

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_half {ε : AE D} {y : Fin B.rank → AE D} (hy : ε • y = y) (x) : hA B x y = cA D ε * hA B x y := by
  rw [← hA_smul_right, hy]

theorem eps_hA {ε : AE D} (h0 : ε * cA D ε = 0) {y : Fin B.rank → AE D} (hy : ε • y = y) (x) :
    ε * hA B x y = 0 := by
  rw [hA_half hy, ← mul_assoc, h0, zero_mul]

theorem hA_smul_zero {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (x) : hA B x y' • y = 0 := by
  rw [← hy, smul_smul, mul_comm, eps_hA h0 hy', zero_smul]

theorem hA_halves {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') : hA B y y' = 0 := by
  rw [← hy, hA_smul, eps_hA h0 hy']

theorem isK_mul {ε : AE D} (h0 : ε * cA D ε = 0) {v y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (hv' : hA B y' v = 0) (hv : hA B v y = 0) {k k' : GA D B} (hk : IsK B v y k)
    (hk' : IsK B v y' k') : IsK B v (y + y') (k * k') := by
  intro x
  rw [mulVec_mul, hk', hk]
  simp only [hA_add, hA_sub, hA_smul, hA_add_right, hv, hv', hA_halves h0 hy' hy, mul_zero, add_zero, sub_zero,
    add_smul, smul_add, mul_comm (hA B x y'), mul_smul, hA_smul_zero h0 hy hy', smul_zero, zero_smul]
  abel

theorem isK_eps {ε : AE D} (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y) {k : GA D B}
    (hk : IsK B v y k) (x) : ε • ((mt B k).mulVec x - x) = -(hA B x v • y) := by
  rw [hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, eps_hA h0 hy, zero_smul, zero_sub, smul_comm, hy]

theorem isK_supp {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y)
    {k : GA D B} (hk : IsK B v y k) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have hc : cA D ε • y = 0 := by rw [← hy, smul_smul, mul_comm, h0, zero_smul]
  rw [add_smul, isK_eps h0 hy hk, hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, ← hA_half hy,
    smul_comm, hc, smul_zero]
  abel

theorem eq_one_of_half {ε : AE D} {u : GA D B} (hu : SuppAt ε B u) (h : ∀ x, ε • ((mt B u).mulVec x - x) = 0) :
    u = 1 := by
  refine mt_ext fun x => ?_
  rw [mt_one, Matrix.one_mulVec, ← sub_eq_zero, ← suppAt_iff_vec.1 hu x, add_smul, h, zero_add]
  refine hA_nondeg fun y => ?_
  have e : (mt B u).mulVec (ε • y) = ε • y := by
    have := h y
    rwa [smul_sub, sub_eq_zero, ← Matrix.mulVec_smul] at this
  rw [hA_smul, ← hA_smul_right, hA_sub]
  conv_lhs => rw [← e]
  rw [hA_mt, e, sub_self]

theorem iA_eq (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]

theorem dual_iA (d : BesselDatum A B ι) (i) (t) : hA B (vecA B (dual d i)) (iA ι t) = 0 :=
  hA_vec_iA (dual_perp d i) t

theorem iA_dual (d : BesselDatum A B ι) (i) (t) : hA B (iA ι t) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, dual_iA, map_zero]

theorem vec_dual (d : BesselDatum A B ι) (i) (x : A.V) : hA B (vecA B (ι x)) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, hA_vec, dual_perp, map_zero, map_zero]

theorem mem_exSet (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t)
    {k : GA D B} (hk : IsK B (vecA B (dual d i)) (iA ι t) k) :
    SuppAt ε B k ∧
    (∀ x : A.V, ε • (actV B k (ι x) - vecA B (ι x)) = 0) ∧
    (∀ l, ε • (actV B k (d.f l) - vecA B (d.f l)) = 0) ∧
    (∀ l, l ≠ i → ε • (actV B k (d.aux l) - vecA B (d.aux l)) = 0) ∧
      ε • (actV B k (d.aux i) - vecA B (d.aux i)) = -iA ι t := by
  have hy : ε • iA ι t = iA ι t := by rw [← iA_smul, ht]
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d
  unfold actV
  refine ⟨isK_supp h1 h0 hy hk, fun x => ?_, fun l => ?_, fun l hl => ?_, ?_⟩
  · rw [isK_eps h0 hy hk, vec_dual, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p2, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_neg hl, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_pos rfl, map_one, one_smul]

theorem exists_k (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t) :
    ∃ k : GA D B, IsK B (vecA B (dual d i)) (iA ι t) k := by
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.exists_continuous_unitaryRootExchangeMap D B ε h0 (vecA B (dual d i))
  exact ⟨_, hK ⟨iA ι t, by rw [← iA_smul, ht], dual_iA d i t⟩⟩

theorem isK_one (v : Fin B.rank → AE D) : IsK B v 0 1 := fun x => by
  rw [mt_one, Matrix.one_mulVec, hA_zero_right, zero_smul, smul_zero, add_zero, sub_zero]

theorem isK_unique {v y : Fin B.rank → AE D} {k k' : GA D B} (h : IsK B v y k) (h' : IsK B v y k') : k = k' :=
  mt_ext fun x => (h x).trans (h' x).symm

def kGrp (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i : Fin (d.ρ + 1)) : Subgroup (GA D B) where
  carrier := {g | ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g}
  one_mem' := ⟨0, smul_zero _, by rw [iA, Matrix.mulVec_zero]; exact isK_one _⟩
  mul_mem' := by
    rintro g g' ⟨t, ht, hg⟩ ⟨t', ht', hg'⟩
    refine ⟨t + t', by rw [smul_add, ht, ht'], ?_⟩
    rw [iA_add]
    exact isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hg'
  inv_mem' := by
    rintro g ⟨t, ht, hg⟩
    have ht' : ε • (-t) = -t := by rw [smul_neg, ht]
    obtain ⟨k, hk⟩ := exists_k d h0 i ht'
    have := isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hk
    rw [iA_neg, add_neg_cancel] at this
    rw [inv_eq_of_mul_eq_one_right (isK_unique this (isK_one _))]
    exact ⟨-t, ht', hk⟩

theorem mulVec_comb (L : Matrix (Fin B.rank) (Fin B.rank) (AE D)) {a : ℕ} (u : Fin a → Fin B.rank → AE D)
    (hu : ∀ i, L.mulVec (u i) = 0) (r : Fin a → AE D) : L.mulVec (∑ i, r i • u i) = 0 := by
  refine Finset.sum_induction _ (fun x => L.mulVec x = 0) (fun x y hx hy => ?_) (Matrix.mulVec_zero _) fun i _ => ?_
  · rw [Matrix.mulVec_add, hx, hy, add_zero]
  · rw [Matrix.mulVec_smul, hu, smul_zero]

theorem mulVec_zero_of (d : BesselDatum A B ι) (L : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0) (a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0)
    (a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0) (x) : L.mulVec x = 0 := by
  obtain ⟨t, e⟩ := (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).2.2 x
  rw [e, iA_eq, Matrix.mulVec_add, Matrix.mulVec_add, mulVec_comb L _ (fun l => a1 (A.frame l)),
    mulVec_comb L _ a3, mulVec_comb L _ a2, add_zero, add_zero]

theorem eq_of_half {ε : AE D} {g k : GA D B} (g1 : SuppAt ε B g) (k1 : SuppAt ε B k)
    (h : ∀ x, ε • ((mt B g).mulVec x - x) = ε • ((mt B k).mulVec x - x)) : k = g := by
  refine inv_mul_eq_one.1 (eq_one_of_half (suppAt_mul (suppAt_inv k1) g1) fun x => ?_)
  have e : ε • (mt B g).mulVec x = ε • (mt B k).mulVec x := by
    have := h x
    rwa [smul_sub, smul_sub, sub_left_inj] at this
  have := congrArg (mt B k⁻¹).mulVec e
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_inv_cancel, ← mulVec_mul] at this
  rw [smul_sub, this, sub_self]

set_option maxHeartbeats 800000 in
theorem exSet_sub (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {g : GA D B}
    (hg : g ∈ d.ExSet ε i) : g ∈ kGrp d h0 i := by
  obtain ⟨g1, g2, g3, g4, y, g5⟩ := hg
  have ht : ε • (-(ε • y)) = -(ε • y) := by rw [smul_neg, smul_smul, h1]
  obtain ⟨k, hk⟩ := exists_k d h0 i ht
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin B.rank) (Fin B.rank) (AE D),
      ∀ x, L.mulVec x = ε • ((mt B g).mulVec x - x) - ε • ((mt B k).mulVec x - x) :=
    ⟨ε • (mt B g - mt B k), fun x => by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← Matrix.sub_mulVec, ← Matrix.smul_mulVec]⟩
  have a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0 := fun x => by
    rw [hL]; exact sub_eq_zero.2 ((g2 x).trans (k2 x).symm)
  have a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0 := fun l => by
    rw [hL]; exact sub_eq_zero.2 ((g3 l).trans (k3 l).symm)
  have a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0 := fun l => by
    rw [hL]
    by_cases hl : l = i
    · subst hl
      refine sub_eq_zero.2 (g5.trans (Eq.symm (k5.trans ?_)))
      rw [iA_neg, neg_neg, iA_smul]; rfl
    · exact sub_eq_zero.2 ((g4 l hl).trans (k4 l hl).symm)
  have a4 : ∀ x, L.mulVec x = 0 := mulVec_zero_of d L a1 a2 a3
  rw [← eq_of_half g1 k1 fun x => sub_eq_zero.1 ((hL x).symm.trans (a4 x))]
  exact ⟨_, ht, hk⟩

theorem mem_Ex_iff : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  intro D A B ι d ε he i g
  have h1 : ε * ε = ε := he.1
  have h0 : ε * cA D ε = 0 := he.2.1
  refine ⟨fun hg => (Subgroup.closure_le (kGrp d h0 i)).2 (fun _ h => exSet_sub d h1 h0 i h) hg, ?_⟩
  rintro ⟨t, ht, hk⟩
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  refine Subgroup.subset_closure ⟨k1, k2, k3, k4, -t, k5.trans ?_⟩
  show _ = ε • iA ι (-t)
  rw [← iA_smul, smul_neg, ht, iA_neg]

end GlobalTheory.RootExch.ExStruct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem interNum_one_lbPow_of_curve {κ : Type} [Field κ] {C : Scheme.{0}} [Algebra κ Γ(C, ⊤)]
    [IsProper (strHom κ C)] {H N : LB C} (hH : IsAmpleLB H) (hd : topologicalKrullDim C = 1)
    (hN : N.IsLB) (n : ℕ) :
    interNum κ (structureModule C) ![lbPow N n] = n * interNum κ (structureModule C) ![N] := by
  induction n with
  | zero =>
    rw [interNum_eq_zero_of_cls_eq_zero κ _ (isLB_vecOne (isLB_lbPow hN 0)) 0
      ((cls_lbPow hN 0 _).trans (zero_nsmul _))]
    simp
  | succ n ih =>
    rw [interNum_one_of_cls_eq_add hH hd (isLB_lbPow hN (n + 1)) (isLB_lbPow hN n) hN
      (by rw [cls_lbPow hN, cls_lbPow hN, succ_nsmul]), ih]
    push_cast
    ring

theorem nefFib_pow_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0})
    (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m →
      (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  intro k _ _ X p hp L m hm
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
      [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
      topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
    intro Z i _ _ κ _ _ _ hd
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    have hAZ := hA.pull_of_isClosedImmersion i
    have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
    have e1 : topSelfIntersection κ ((L.pow m).B.pull i) 1 =
        interNum κ (structureModule Z) ![lbPow (L.B.pull i) m] :=
      interNum_congr_cls κ _ (fun _ => LB.isLB_pull (L.pow m).isLB i)
        (isLB_vecOne (isLB_lbPow hN m)) fun j => by
          fin_cases j
          exact (cls_pull (L.pow m).isLB i _).trans
            ((congrArg (pull i) (cls_lbPow L.isLB m (L.pow m).isLB)).trans
              ((map_nsmul (pull i) m _).trans (cls_lbPow hN m _).symm))
    have e2 : topSelfIntersection κ (L.B.pull i) 1 = interNum κ (structureModule Z) ![L.B.pull i] := by
      rw [topSelf_def]
      congr 1
      funext j
      fin_cases j
      rfl
    rw [e1, e2]
    exact interNum_one_lbPow_of_curve hAZ hd hN m
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  constructor
  · intro h Z i _ _ κ _ _ _ hd
    have h' := h Z i κ hd
    rw [key Z i κ hd] at h'
    exact (mul_nonneg_iff_of_pos_left hm').1 h'
  · intro h Z i _ _ κ _ _ _ hd
    rw [key Z i κ hd]
    exact mul_nonneg hm'.le (h Z i κ hd)

end GlobalTheory.ArInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishing
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.KernelCut

private theorem subsingleton_kernel_sections_of_app_injective {Y : Scheme.{0}} {M N : Y.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (hφ : ∀ t, φ.app V t = 0 → t = 0) : Subsingleton Γ(kernel φ, V) := by
  have hmono : Mono ((kernel.ι φ).app V) := by
    have h1 : Mono ((Scheme.Modules.toPresheaf Y).map (kernel.ι φ)) := inferInstance
    exact (NatTrans.mono_iff_mono_app _).1 h1 (Opposite.op V)
  have hinj := (AddCommGrpCat.mono_iff_injective _).1 hmono
  have key : ∀ c : Γ(kernel φ, V), c = 0 := by
    intro c
    apply hinj
    rw [map_zero]
    apply hφ
    have h2 : (kernel.ι φ ≫ φ).app V c = 0 := by simp
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h2
    exact h2
  exact ⟨fun a b => by rw [key a, key b]⟩

private theorem notMem_support_of_subsingleton_sections {Y : Scheme.{0}} (K : Y.Modules) {x : Y} (W : Y.Opens)
    (hxW : x ∈ W) (h : ∀ V : Y.Opens, V ≤ W → Subsingleton Γ(K, V)) : x ∉ support K := by
  unfold support
  simp only [Set.mem_ofPred_eq, not_nontrivial_iff_subsingleton]
  have key : ∀ c : K.presheaf.stalk x, c = 0 := by
    intro c
    obtain ⟨U, hxU, t, rfl⟩ := K.presheaf.exists_germ_eq c
    rw [← K.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) x ⟨hxU, hxW⟩ t]
    have := h (U ⊓ W) inf_le_right
    rw [Subsingleton.elim (K.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op t) 0, map_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem notMem_support_kernel_cutHom : ∀ {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (s : L.Sec) (G : Y.Modules) [G.IsQuasicoherent], ∀ x ∈ Out.nonzeroLocus s, x ∉ support (kernel (cutHom G hL s)) := by
  intro Y L hL s G _ x hx
  have hx' : x ∈ ⨆ k, Y.basicOpen (s.f k) := by
    unfold Out.nonzeroLocus at hx
    exact hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  have hle : Y.basicOpen (s.f k) ≤ Out.nonzeroLocus s := by
    unfold Out.nonzeroLocus
    exact le_iSup (fun j => Y.basicOpen (s.f j)) k
  refine notMem_support_of_subsingleton_sections _ (Y.basicOpen (s.f k)) hk fun V hV => ?_
  have hVU : V ≤ L.U k := hV.trans (Y.basicOpen_le _)
  have hmb := isMulBy_cutHom G hL s
  obtain ⟨e, he⟩ := hmb k V hVU
  have hunit : IsUnit (resG Y hVU (s.f k)) := by
    have h3 := isUnit_resG_zfun (zofSec s) k hVU
      (by rw [nonzeroLocus_zofSec hL s]; exact hV.trans hle)
    simpa using h3
  refine subsingleton_kernel_sections_of_app_injective _ V fun t ht => ?_
  rw [he] at ht
  have h4 : e t = 0 := hunit.smul_eq_zero.1 ht
  exact e.injective (h4.trans e.map_zero.symm)

end GlobalTheory.KernelCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmEqSelfOfLatticeStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem om_eq_self_of_lattice_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D), IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → splitFacO χS χT x y = 1 → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), actO S T g⁻¹ h⁻¹ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f) → om (g, h) f = f := by
  intro D ψ S T χS χT om hW e he g h hg hh x y hx hy h1 hL f hf hfix
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hdual
  have hfin := @GlobalTheory.SplitScalar.latO_fin D S T (L0c D S) (L0c D T)
  have key := om_eq_sum hW he hf hfix hg hh hx hy (R := {0})
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨hL 0 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩)
    (fun w hw hwe => by
      refine ⟨0, ⟨Finset.mem_singleton_self _, ?_⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩
      rw [sub_zero, hdual w (GlobalTheory.SplitScalar.half_fin he hwe)]
      intro u hu
      rw [← symplO_actO S T g⁻¹ h⁻¹]
      exact (hdual _ (hfin hw)).1 hw _ (hL u hu))
    (fun w hw _ => hL w hw)
  rw [key, h1, Finset.sum_singleton, Finset.card_singleton, GlobalTheory.SplitScalar.heisO_zero]
  simp

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidt
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.SobHS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_orthonormal_expansion {ι : Type} [Fintype ι] (f : ι → H) :
    ∃ (m : ℕ) (h : Fin m → H) (φ : ι → Fin m → ℂ), Orthonormal ℂ h ∧ (∀ j, f j = ∑ p, φ j p • h p) ∧
      ∀ j, ∑ p, ‖φ j p‖ ^ 2 = ‖f j‖ ^ 2 := by
  let U : Submodule ℂ H := Submodule.span ℂ (Set.range f)
  haveI : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  let b := stdOrthonormalBasis ℂ U
  let u : ι → U := fun j => ⟨f j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨_, fun p => (b p : H), fun j p => ⟪b p, u j⟫_ℂ, b.orthonormal.comp_linearIsometry U.subtypeₗᵢ,
    fun j => ?_, fun j => b.sum_sq_norm_inner_right (u j)⟩
  have := congrArg Subtype.val (b.sum_repr' (u j))
  simpa using this.symm

theorem integral_sq_sum {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {μ : Measure (UJ ε)} {d : ℝ}
    (hd : IsFdeg μ σ d) {m : ℕ} {h : Fin m → H} (hh : Orthonormal ℂ h) (y : Fin m → H) :
    Integrable (fun g : UJ ε => ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2) μ ∧
      ∫ g : UJ ε, ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 ∂μ = (∑ p, ‖y p‖ ^ 2) / d := by
  have e : ∀ g : UJ ε, ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
      ∑ p, ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g) := by
    intro g
    rw [← Finset.sum_mul_sum, ← star_sum, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  have i1 : ∀ p, Integrable (fun g : UJ ε => ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g)) μ :=
    fun p => integrable_finset_sum _ fun q _ => (hd.2 _ _ _ _).1
  have i2 : Integrable (fun g : UJ ε => ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) μ := by
    simp only [e]
    exact integrable_finset_sum _ fun p _ => i1 p
  refine ⟨by simpa only [RCLike.re_to_complex, Complex.ofReal_re] using i2.re, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [e]
  rw [integral_finset_sum _ fun p _ => i1 p]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finset_sum _ fun q _ => (hd.2 _ _ _ _).1]
  simp only [(hd.2 _ _ _ _).2, orthonormal_iff_ite.1 hh]
  rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
  simp [inner_self_eq_norm_sq_to_K]

theorem sobolev_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨S, C, hS, hC, H1⟩ := GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary n ε
  obtain ⟨d, hd⟩ := hσ.2.2.2.1
  have hd0 := hd.1
  refine ⟨S, C * S.length / d, hS, by positivity, fun ι _ f x A hA hx hb => ?_⟩
  obtain ⟨m, h, φ, hh, hf, hφ⟩ := exists_orthonormal_expansion f
  let F : List (Mx n) → Mx n → ℂ := fun l g => ∑ j, ⟪f j, σ g (Dw σ l (x j))⟫_ℂ
  have eF : ∀ l g, F l g = ∑ p, ⟪h p, σ g (∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j))⟫_ℂ := by
    intro l g
    simp only [F, map_sum, map_smul, inner_sum, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf j, sum_inner]
    simp only [inner_smul_left]
  have hI := fun l => integral_sq_sum hd hh fun p => ∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j)
  simp only [← eF] at hI
  have key := H1 F (fun l _ => continuousOn_finset_sum _ fun j _ =>
      (innerSL ℂ (f j)).continuous.comp_continuousOn (hσ.1.2.2 _)) ?_ fun l _ => (hI l).1
  · have e1 : F [] 1 = ∑ j, ⟪f j, x j⟫_ℂ := by simp only [F, sigma_one hσ.1]; rfl
    rw [e1] at key
    refine key.trans ?_
    have h2 : (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum ≤
        (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).length • ((A * ∑ j, ‖f j‖ ^ 2) / d) := by
      refine List.sum_le_card_nsmul _ _ fun r hr => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
      rw [(hI l).2]
      refine div_le_div_of_nonneg_right ?_ hd0.le
      refine (Finset.sum_le_sum fun p _ => hb l hl _).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [RCLike.norm_conj, hφ]
    rw [List.length_map, nsmul_eq_mul] at h2
    refine (mul_le_mul_of_nonneg_left h2 hC).trans (le_of_eq ?_)
    ring
  · intro l hl X hX g hg
    have e : ∀ t : ℝ, F l (g * NormedSpace.exp (t • X)) =
        ∑ j, ⟪f j, σ g (σ (NormedSpace.exp (t • X)) (Dw σ l (x j)))⟫_ℂ := fun t => by
      simp only [F, sigma_mul hσ.1 hg (exp_mem_UJ hX t)]
    simp only [e]
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_orbit hσ.1 ((hx j).word hσ.1 hl) hX 0
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ.1] at h1
    exact (((innerSL ℂ (f j)).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1

end GlobalTheory.TypeSum.SobHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  first | exact @GlobalTheory.PairInfTypes.infTypesAt | exact GlobalTheory.PairInfTypes.infTypesAt | (intros; apply GlobalTheory.PairInfTypes.infTypesAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOneVectorStepCompatibleChangeOfBasisStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryOneVectorStep_compatible_changeOfBasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E) (eP : HA (AF F) σ J ≃* HA (AF F) σ J₂) (eQ : HA (AF F) σ J' ≃* HA (AF F) σ J₂') (μ : Measure (HA (AF F) σ J)) (μ' : Measure (HA (AF F) σ J')), StepData σ J x a B J' → J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) → J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) * J' * (Q : Matrix (Fin M) (Fin M) E) → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → (∀ g, FrameRel J J₂ (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) g (eP g)) → (∀ g, FrameRel J' J₂' (Q : Matrix (Fin M) (Fin M) E) g (eQ g)) → StepRel s σ J x a B J' μ μ' → StepData σ J₂ x₂ a B₂ J₂' ∧ StepRel s σ J₂ x₂ a B₂ J₂' (μ.map eP) (μ'.map eQ) := by
  first | exact @GlobalTheory.GaugeEx.stepRel_basis | exact GlobalTheory.GaugeEx.stepRel_basis | (intros; apply GlobalTheory.GaugeEx.stepRel_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumOrientedExists
section
open Formalism.BasicNotions Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem vacuum_oriented_exists : ∀ D : D7, VacExistsO D := GlobalTheory.VacuumO.vacExists

end GlobalTheory.Member
end

