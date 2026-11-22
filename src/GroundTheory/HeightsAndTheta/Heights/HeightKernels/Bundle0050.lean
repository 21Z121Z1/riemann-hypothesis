import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcResidueExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField StackedExceptionalFirstGeometric

noncomputable section

namespace StackedExceptionalResidueExists

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i}

theorem exists_mem_not_mem (hlt : F'.lattice < F.lattice) :
    ∃ φc ∈ dualLattice F', φc ∉ dualLattice F := by
  by_contra! h
  have h1 : (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr fun φ hφ => h φ hφ
  rw [DualLatticeIndex.proof K i F F' hlt.le] at h1
  have h2 := AddSubgroup.relIndex_eq_one.mp h1
  exact hlt.not_ge fun x hx => h2 hx

def annIdeal (F : HermLattice K i) (φc : Fin i → K) : Ideal (𝓞 K) where
  carrier := {μ | algebraMap (𝓞 K) K μ • φc ∈ dualLattice F}
  add_mem' {a b} ha hb := by
    show algebraMap (𝓞 K) K (a + b) • φc ∈ dualLattice F
    rw [map_add, add_smul]
    exact add_mem ha hb
  zero_mem' := by
    show algebraMap (𝓞 K) K 0 • φc ∈ dualLattice F
    rw [map_zero, zero_smul]
    exact zero_mem _
  smul_mem' c x hx := by
    show algebraMap (𝓞 K) K (c * x) • φc ∈ dualLattice F
    rw [map_mul, mul_smul]
    exact smul_mem_dual F c hx

theorem mem_annIdeal {φc : Fin i → K} {μ : 𝓞 K} :
    μ ∈ annIdeal F φc ↔ algebraMap (𝓞 K) K μ • φc ∈ dualLattice F := Iff.rfl

theorem annIdeal_isMaximal (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) : (annIdeal F φc).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hc' ?_, fun J x hle hx hxJ => ?_⟩
  · have := mem_annIdeal.mp h
    rwa [map_one, one_smul] at this
  obtain ⟨l, hl⟩ := exists_sub_mem_dual hlt hcov (smul_mem_dual F' x hc) (mem_annIdeal.not.mp hx) hc
  have h1 : 1 - l * x ∈ annIdeal F φc := by
    rw [mem_annIdeal, map_sub, map_one, map_mul, sub_smul, one_smul, mul_smul]
    exact hl
  have h2 := J.add_mem (hle h1) (J.mul_mem_left l hxJ)
  rwa [sub_add_cancel] at h2

theorem mk_eq_of {φc φ : Fin i → K} {l l' : 𝓞 K} (h : φ - algebraMap (𝓞 K) K l • φc ∈ dualLattice F)
    (h' : φ - algebraMap (𝓞 K) K l' • φc ∈ dualLattice F) :
    Ideal.Quotient.mk (annIdeal F φc) l = Ideal.Quotient.mk (annIdeal F φc) l' := by
  rw [Ideal.Quotient.eq, mem_annIdeal, map_sub, sub_smul]
  have e : algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l' • φc =
      (φ - algebraMap (𝓞 K) K l' • φc) - (φ - algebraMap (𝓞 K) K l • φc) := by abel
  rw [e]
  exact sub_mem h' h

def coeff (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') : 𝓞 K :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose

theorem coeff_spec (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') :
    (φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc ∈ dualLattice F :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose_spec

def rhoDual (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) :
    dualLattice F' →+ 𝓞 K ⧸ annIdeal F φc where
  toFun φ := Ideal.Quotient.mk _ (coeff hlt hcov hc hc' φ)
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk (annIdeal F φc))]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' 0) ?_
    rw [map_zero, zero_smul, sub_zero]
    exact zero_mem _
  map_add' φ ψ := by
    rw [← map_add]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' (φ + ψ)) ?_
    have e : ((φ + ψ : dualLattice F') : Fin i → K) - algebraMap (𝓞 K) K
        (coeff hlt hcov hc hc' φ + coeff hlt hcov hc hc' ψ) • φc =
        ((φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc) +
        ((ψ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' ψ) • φc) := by
      rw [Submodule.coe_add, map_add, add_smul]
      abel
    rw [e]
    exact add_mem (coeff_spec hlt hcov hc hc' φ) (coeff_spec hlt hcov hc hc' ψ)

theorem rhoDual_eq (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') (l : 𝓞 K)
    (h : (φ : Fin i → K) - algebraMap (𝓞 K) K l • φc ∈ dualLattice F) :
    rhoDual hlt hcov hc hc' φ = Ideal.Quotient.mk _ l :=
  mk_eq_of (coeff_spec hlt hcov hc hc' φ) h

end StackedExceptionalResidueExists

open StackedExceptionalResidueExists in

theorem DualStackedExcResidueExists.proof (hσ : DualLatticeModPrime.Statement) :
    DualStackedExcResidueExists.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hlt hcov _
  obtain ⟨φc, hc, hc'⟩ := exists_mem_not_mem hlt
  set 𝔭 := annIdeal F φc with h𝔭
  have hmax : 𝔭.IsMaximal := annIdeal_isMaximal hlt hcov hc hc'
  let _ : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  obtain ⟨σ, hσs, hσl⟩ := hσ K i F 𝔭 hmax
  set ρ' := rhoDual hlt hcov hc hc' with hρ'
  have hker : ∀ φ : dualLattice F', ρ' φ = 0 ↔ (φ : Fin i → K) ∈ dualLattice F := by
    intro φ
    have hs := coeff_spec hlt hcov hc hc' φ
    change Ideal.Quotient.mk 𝔭 (coeff hlt hcov hc hc' φ) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_annIdeal]
    constructor
    · intro h
      have := add_mem hs h
      rwa [sub_add_cancel] at this
    · intro h
      have := sub_mem h hs
      rwa [sub_sub_cancel] at this
  have hsurj : Function.Surjective ρ' := by
    intro x
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨⟨algebraMap (𝓞 K) K l • φc, smul_mem_dual F' l hc⟩, rhoDual_eq hlt hcov hc hc' _ l ?_⟩
    show algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l • φc ∈ dualLattice F
    rw [sub_self]
    exact zero_mem _
  have hcard : Nat.card (𝓞 K ⧸ 𝔭) = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup := by
    rw [← DualLatticeIndex.proof K i F F' hlt.le]
    have hk : (dualLattice F).toAddSubgroup.addSubgroupOf (dualLattice F').toAddSubgroup = ρ'.ker := by
      ext φ
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hker]
      rfl
    rw [AddSubgroup.relIndex, hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj]
    exact (Nat.card_congr (Equiv.Set.univ _)).symm
  refine ⟨𝓞 K ⧸ 𝔭, inferInstance, Fintype.ofFinite _, fun t => ρ' (b' t), fun t => σ (b t),
    ⟨Ideal.Quotient.mk 𝔭, ρ', σ, Ideal.Quotient.mk_surjective, hsurj, hσs, hker, ?_, hσl,
      fun t => rfl, fun t => rfl⟩, ?_⟩
  · intro μ φ ψ h
    rw [rhoDual_eq hlt hcov hc hc' ψ (μ * coeff hlt hcov hc hc' φ), map_mul]
    · rfl
    rw [h, map_mul, mul_smul, ← smul_sub]
    exact smul_mem_dual F μ (coeff_spec hlt hcov hc hc' φ)
  · rw [← hcard]
    exact Fintype.card_eq_nat_card

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphBihomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphBihomogeneous

section Parts

variable {T : Type} [Fintype T]

def bideg (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) : ℕ × ℕ :=
  (∑ t : T, m ⟨Sum.inl (), t⟩, ∑ t : T, m ⟨Sum.inr (), t⟩)

def bipart (f : MRing (stackedBlocks T)) (p : ℕ × ℕ) : MRing (stackedBlocks T) :=
  ∑ m ∈ f.support.filter (fun m => bideg m = p), monomial m (coeff m f)

theorem sum_bipart (f : MRing (stackedBlocks T)) : f = ∑ p ∈ f.support.image bideg, bipart f p := by
  classical
  unfold bipart
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact (support_sum_monomial_coeff f).symm

theorem isMultiHomog_bipart (f : MRing (stackedBlocks T)) (p : ℕ × ℕ) :
    IsMultiHomog (bipart f p) (bidegree p.1 p.2) := by
  classical
  intro m hm κ
  obtain ⟨m', hm', hmm'⟩ := Finset.mem_biUnion.mp (support_sum hm)
  obtain rfl : m = m' := Finset.mem_singleton.mp (support_monomial_subset hmm')
  have hp : bideg m = p := (Finset.mem_filter.mp hm').2
  rcases κ with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

def secW (s : Σ κ, stackedBlocks T κ) : ℕ := Sum.elim (fun _ => 0) (fun _ => 1) s.1

theorem sum_eq_bideg (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) :
    ∑ s, m s = (bideg m).1 + (bideg m).2 := by
  rw [Fintype.sum_sigma, Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, bideg]
  rfl

theorem sum_secW_eq_bideg (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) :
    ∑ s, secW s * m s = (bideg m).2 := by
  rw [Fintype.sum_sigma, Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, bideg, secW, Sum.elim_inl, Sum.elim_inr, zero_mul, one_mul,
    Finset.sum_const_zero, zero_add]
  rfl

end Parts

section Eval

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}

def formEvalFrac (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    MRing (stackedBlocks T) →+* ProjField K i :=
  (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)).comp (stackedFormEval b b')

def biEval (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    MRing (stackedBlocks T) →+* MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) :=
  eval₂Hom (Int.castRingHom (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))))
    fun s => C (C (formEvalFrac b b' (X s)) * X ()) * X () ^ secW s

theorem biEval_monomial [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) (c : ℤ) :
    biEval b b' (monomial m c) =
      C (C (formEvalFrac b b' (monomial m c)) * X () ^ (∑ s, m s)) * X () ^ (∑ s, secW s * m s) := by
  have hE : formEvalFrac b b' (monomial m c) = (c : ProjField K i) * ∏ s, formEvalFrac b b' (X s) ^ m s := by
    rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
    simp [map_pow]
  rw [hE, monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [biEval, coe_eval₂Hom, eval₂_X, map_pow, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, eq_intCast, map_intCast]
  ring

theorem formEvalFrac_first (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (t : T) : formEvalFrac b b' (X ⟨Sum.inl (), t⟩) = dualLatticeCoord b' ⟨(), t⟩ := by
  have h : (X ⟨Sum.inl (), t⟩ : MRing (stackedBlocks T)) = graphFirst t := rfl
  rw [formEvalFrac, RingHom.comp_apply, h, DualStackedExcLeadExample.stackedFormEval_first, dualLatticeCoord]

theorem formEvalFrac_second (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    {a : T → ℤ} (hb : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (t : T) :
    formEvalFrac b b' (X ⟨Sum.inr (), t⟩) = (a t : ProjField K i) * dualLatticeCoord b' ⟨(), t⟩ := by
  have h : (X ⟨Sum.inr (), t⟩ : MRing (stackedBlocks T)) = graphSecond t := rfl
  rw [formEvalFrac, RingHom.comp_apply, h, DualStackedExcLeadExample.stackedFormEval_second, hb t,
    dualLatticeCoord, ← map_intCast (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)), ← map_mul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, zsmul_eq_mul, map_mul, ← mul_assoc, map_intCast]

theorem biEval_eq_zero [Fintype T] [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T ℤ (dualLattice F')) {a : T → ℤ}
    (hb : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {f : MRing (stackedBlocks T)}
    (hf : f ∈ stackedGraph b' a) : biEval b b' f = 0 := by
  let Q : MRing (dualBlocks T) ⧸ dualIdeal b' →+* MvPolynomial Unit (ProjField K i) :=
    Ideal.Quotient.lift (dualIdeal b')
      (mConeMap (dualLatticeCoord b') : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i))
      (fun g hg => RingHom.mem_ker.mp hg)
  have hg : ∀ t : T, linForm (ι := dualBlocks T) (ι₂ := dualBlocks T) (stackedDiag a) ⟨(), t⟩ =
      C (a t) * X ⟨(), t⟩ := fun t => by
    simp [linForm, stackedDiag, apply_ite C, ite_mul, Finset.sum_ite_eq]
  have hcomp : (map Q).comp (graphMap (dualIdeal b') (linForm (stackedDiag a))) = biEval b b' := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [biEval]
    · rintro ⟨(u | u), t⟩ <;> obtain ⟨⟩ := u
      · have h1 := formEvalFrac_first b b' t
        simp only [RingHom.comp_apply, graphMap, coe_eval₂Hom, eval₂_X, map_C, Q,
          Ideal.Quotient.lift_mk, biEval, secW, h1] at *
        simp [mConeMap]
      · have h2 := formEvalFrac_second b b' hb t
        simp only [RingHom.comp_apply, graphMap, coe_eval₂Hom, eval₂_X, map_mul, map_C, Q, hg t,
          Ideal.Quotient.lift_mk, biEval, secW, h2] at *
        simp [mConeMap, map_mul]
        ring
  have hf0 : graphMap (dualIdeal b') (linForm (stackedDiag a)) f = 0 := RingHom.mem_ker.mp hf
  rw [← hcomp, RingHom.comp_apply, hf0, map_zero]

end Eval

section Final

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]

theorem coeff_C_mul_X_pow_unit {R : Type*} [CommSemiring R] (r : R) (n e : ℕ) :
    coeff (Finsupp.single () e) (C r * X () ^ n : MvPolynomial Unit R) = if n = e then r else 0 := by
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  by_cases h : n = e
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (by simpa using congrArg (fun g : Unit →₀ ℕ => g ()) h')

theorem stackedFormEval_bipart (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T ℤ (dualLattice F')) {a : T → ℤ}
    (hb : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {f : MRing (stackedBlocks T)}
    (hf : f ∈ stackedGraph b' a) (p : ℕ × ℕ) : stackedFormEval b b' (bipart f p) = 0 := by
  apply IsFractionRing.injective (MvPolynomial (Fin i) K) (ProjField K i)
  rw [map_zero]
  change formEvalFrac b b' (bipart f p) = 0
  have h0 := biEval_eq_zero b b' hb hf
  rw [← support_sum_monomial_coeff f, map_sum] at h0
  simp_rw [biEval_monomial] at h0
  have h1 := congrArg (fun q => coeff (Finsupp.single () (p.1 + p.2)) (coeff (Finsupp.single () p.2) q)) h0
  simp only [coeff_sum, coeff_C_mul_X_pow_unit, apply_ite (coeff (Finsupp.single () (p.1 + p.2))),
    coeff_zero] at h1
  rw [← h1, bipart, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_eq_bideg, sum_secW_eq_bideg]
  obtain ⟨d, e⟩ := p
  obtain ⟨d', e'⟩ := bideg m
  by_cases he : e' = e
  · subst he
    simp
  · simp [he]

end Final

end StackedGraphBihomogeneous

open StackedGraphBihomogeneous in

theorem DualStackedGraphBihomog.proof : DualStackedGraphBihomog.Statement := by
  intro K _ _ i F F' T _ _ b b' a hb f hf
  exact ⟨f.support.image bideg, bipart f, sum_bipart f,
    fun p _ => ⟨isMultiHomog_bipart f p, stackedFormEval_bipart b b' hb hf p⟩⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdModelRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

open StandardModelDualRank in

theorem DualStdModelRank.proof : DualStdModelRank.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hrange : Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)) = Set.range (u K i) := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟩, j⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(), j⟩, rfl⟩
  rw [hrange] at hΦ
  refine ⟨?_, ?_⟩
  · change dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i ≠ 0
    exact mul_ne_zero (coord_ne_zero b c) S_ne_zero
  have hr : (fun t : T => dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      fun t => w b t * (w b c)⁻¹ := by
    funext t
    change dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i /
      (dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i) = _
    rw [← div_eq_mul_inv, w, w, mul_div_mul_right (_ * dualStdModelS K i) _ (T_ne_zero (K := K) (i := i))]
  rw [hr]
  let B := Module.finBasis ℚ K
  let M' := Algebra.adjoin Φ₀ (Set.range (embK K i))
  have hM' : Subalgebra.toSubmodule M' = Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) :=
    adjoin_embK_eq_span B Φ₀
  have hfg : (Subalgebra.toSubmodule M').FG := by
    rw [hM']
    exact Submodule.fg_span (Set.finite_range _)
  have hwM' : ∀ t, w b t ∈ M' := fun t => by
    rw [w_eq]
    refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, rfl⟩) ?_
    have hu : u K i j ∈ (algebraMap Φ₀ (dualStdModelField K i)).fieldRange := by
      rw [hΦ]
      exact Subfield.subset_closure ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := RingHom.mem_fieldRange.mp hu
    rw [← hg]
    exact Subalgebra.algebraMap_mem _ g
  have hMM' : Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) ≤ M' := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    exact Subalgebra.mul_mem _ (hwM' t) (Subalgebra.inv_mem_of_algebraic M' (x := ⟨w b c, hwM' c⟩)
      (IsIntegral.of_mem_of_fg M' hfg _ (hwM' c)).isAlgebraic)
  have hβM : ∀ a, embK K i a ∈ Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) := fun a => by
    obtain ⟨N, hN, n, hn⟩ := exists_int_comb b c a
    have hNΩ : (N : dualStdModelField K i) ≠ 0 := by
      rw [← map_intCast (embK K i)]
      exact (map_ne_zero_iff _ (embK K i).injective).mpr (Int.cast_ne_zero.mpr hN)
    have he : embK K i a =
        algebraMap Φ₀ _ ((N : Φ₀)⁻¹) * ∑ t, (n t : dualStdModelField K i) * (w b t * (w b c)⁻¹) := by
      rw [map_inv₀, map_intCast]
      simp only [← mul_assoc, ← Finset.sum_mul, hn]
      field_simp [w_ne_zero b c]
    rw [he]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ fun t _ =>
      Subalgebra.mul_mem _ (intCast_mem _ _) (Algebra.subset_adjoin ⟨t, rfl⟩))
  have hMeq : Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹)) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by
    apply le_antisymm
    · rw [← hM']
      exact fun x hx => hMM' hx
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hβM (B k)
  rw [← Subalgebra.finrank_toSubmodule, hMeq, finrank_span_eq_card (linIndep B Φ₀ hΦ), Fintype.card_fin]

end

end GroundTheory.Heights₂.Heights
end

