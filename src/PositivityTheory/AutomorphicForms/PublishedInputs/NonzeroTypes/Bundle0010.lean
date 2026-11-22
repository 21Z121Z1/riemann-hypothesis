import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTzInj
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem KC_anti {n r r' : ℕ} (h : r ≤ r') : KC k n r' ⊆ KC k n r := by
  rintro g ⟨hg, hP⟩
  refine ⟨hg, fun i j => ?_⟩
  obtain ⟨y, hy, e⟩ := hP i j
  exact ⟨y, Ideal.pow_le_pow_right h hy, e⟩

theorem eq_zero_of_inPow {x : k} (hx : ∀ r, InPow r x) : x = 0 := by
  obtain ⟨y, -, rfl⟩ := hx 0
  have hy : ∀ r : ℕ, y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
    intro r
    obtain ⟨z, hz, e⟩ := hx r
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  have hmem : y ∈ ⨅ r : ℕ, IsLocalRing.maximalIdeal 𝒪[k] ^ r := (Submodule.mem_iInf _).2 hy
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top] at hmem
  rw [(Ideal.mem_bot).1 hmem, map_zero]

theorem eq_one_of_KC {n : ℕ} {g : GL (Fin n) k} (hg : ∀ r, g ∈ KC k n r) : g = 1 := by
  ext i j
  have h := eq_zero_of_inPow (fun r => (hg r).2 i j)
  rw [sub_eq_zero] at h
  rw [h]
  simp [Matrix.one_apply]

theorem exists_KC_subset {n : ℕ} (hsub : ∀ r, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r))
    (hop : ∀ r, IsOpen (KC k n r)) (U : Set (GL (Fin n) k)) (hU : IsOpen U) (h1 : (1 : GL (Fin n) k) ∈ U) :
    ∃ r, KC k n r ⊆ U := by
  have hcl : ∀ r, IsClosed (KC k n r) := by
    intro r
    have := Subgroup.isClosed_of_isOpen (KCg k n r) (by rw [hsub r]; exact hop r)
    rwa [hsub r] at this
  have hst : (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ r, (KC k n r ∩ Uᶜ) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg.2
    have h1' : g = 1 := eq_one_of_KC fun r => (hg' r).1
    exact (hg' 0).2 (h1' ▸ h1)
  have hdt : Directed (· ⊇ ·) (fun r => KC k n r ∩ Uᶜ) := by
    intro a b
    exact ⟨max a b, Set.inter_subset_inter_left _ (KC_anti (le_max_left a b)),
      Set.inter_subset_inter_left _ (KC_anti (le_max_right a b))⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).elim_directed_family_closed
    (fun r => KC k n r ∩ Uᶜ) (fun r => (hcl r).inter hU.isClosed_compl) hst hdt
  refine ⟨r, fun g hg => ?_⟩
  by_contra hgU
  have : g ∈ (KO k (Fin n) : Set (GL (Fin n) k)) ∩ (KC k n r ∩ Uᶜ) := ⟨hg.1, hg, hgU⟩
  rw [hr] at this
  exact this

variable {n : ℕ} (G : Grp k n)

theorem conj_unip (ϖ : kˣ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    (G.zEl ϖ)⁻¹ * u * G.zEl ϖ ∈ unipRad k G.e := by
  have hz : G.zEl ϖ ∈ Subgroup.normalizer (unipRad k G.e : Set (GL (Fin n) k)) :=
    leviEmb_mem_normalizer k G.e _
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hz) u).1 hu
  simpa using this

theorem mem_zN (ϖ : kˣ) (u : ↥G.NO) :
    u ∈ G.zN ϖ 1 ↔ ∃ w ∈ G.NO, G.zEl ϖ * w * (G.zEl ϖ)⁻¹ = (u : GL (Fin n) k) := by
  simp [Grp.zN, Subgroup.mem_subgroupOf, Subgroup.mem_map, MulAut.conj_apply]

theorem PJ_zero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) :
    G.PJ π r 0 = 0 := by
  simp [Grp.PJ]

end UpperTheory.TNZ.Grp.P_TzInj

namespace UpperTheory.TNZ.Grp

open P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_TzInj {n : ℕ} (G : Grp k n) : TorusCentreInjectiveProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V _ _ π hs x hx hT
  have h3 : ∀ a b c : GL (Fin n) k, ∀ v : V, π (a * b * c) v = π a (π b (π c v)) := fun a b c v => by
    rw [map_mul, map_mul]; rfl
  have hQfin : Finite (↥G.NO ⧸ G.zN ϖ 1) := (hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw ϖ hϖ 1).1
  let _ : Fintype (↥G.NO ⧸ G.zN ϖ 1) := Fintype.ofFinite _

  have hsum : ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = 0 := by
    have e0 : π (G.zEl ϖ)⁻¹ (G.Tz π ϖ 1 x) = 0 := by rw [hT, map_zero]
    have e1 : G.Tz π ϖ 1 x = ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
        π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ 1) x) := by
      unfold Grp.Tz
      exact finsum_eq_sum_of_fintype _
    rw [e1, map_sum] at e0
    rw [← e0]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h3, pow_one]

  let U : Set (GL (Fin n) k) := {g | π g x = x} ∩ ⋂ c : ↥G.NO ⧸ G.zN ϖ 1,
    {g | π g (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x}
  have hUo : IsOpen U := (hs x).inter (isOpen_iInter_of_finite fun c => hs _)
  have hU1 : (1 : GL (Fin n) k) ∈ U := by
    refine ⟨by simp, Set.mem_iInter.2 fun c => ?_⟩
    simp
  obtain ⟨r0, hr0⟩ := exists_KC_subset (fun r => (hKC hccB r).1) (fun r => (hKC hccB r).2.2.1) U hUo hU1
  set r := max r0 G.lev with hr
  have hrl : G.lev ≤ r := le_max_right _ _
  have hKCr : KC k n r ⊆ U := (KC_anti (le_max_left _ _)).trans hr0
  have hPJ' := hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC V π r hrl
  have hJfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := hPJ'.1
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hlin : ∀ f : ↥G.NO ⧸ G.zN ϖ 1 → V,
      G.PJ π r (∑ c, f c) = ∑ c, G.PJ π r (f c) := by
    intro f
    simp only [Grp.PJ, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  have hsum' := congrArg (G.PJ π r) hsum
  rw [hlin, PJ_zero] at hsum'
  let c1 : ↥G.NO ⧸ G.zN ϖ 1 := QuotientGroup.mk (1 : ↥G.NO)
  rw [Finset.sum_eq_single c1] at hsum'
  ·
    have hu1 : (Quotient.out c1 : ↥G.NO) ∈ G.zN ϖ 1 := by
      have h : (QuotientGroup.mk (Quotient.out c1) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        Quotient.out_eq c1
      have := QuotientGroup.eq.1 h
      simpa using this
    obtain ⟨w, hw, hwe⟩ := (mem_zN G ϖ _).1 hu1
    have hyw : (G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ = w := by
      rw [← hwe]; group
    have hfix1 : π ((G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = x := by
      rw [hyw, hx w (hlU.1 w hw).1, (hlU.1 w hw).2, one_smul]
    rw [hfix1] at hsum'
    have hxfix : ∀ u ∈ KC k n r, π u x = x := fun u hu => (hKCr hu).1
    rw [(hPJ'.2 x hxfix).2.2 hx] at hsum'
    have hcard : (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact (smul_eq_zero.1 hsum').resolve_left hcard
  ·
    intro c _ hc
    have hfix : ∀ u ∈ KC k n r, π u (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
        π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x :=
      fun u hu => Set.mem_iInter.1 (hKCr hu).2 c
    have hmem : ((Quotient.out c : ↥G.NO) : GL (Fin n) k) ∈ unipRad k G.e ⊓ KO k (Fin n) := (Quotient.out c).2
    have hyU := conj_unip G ϖ (Subgroup.mem_inf.1 hmem).1
    have hyK : (G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ ∉ KO k (Fin n) := by
      intro hK
      apply hc
      have hin : (Quotient.out c : ↥G.NO) ∈ G.zN ϖ 1 := by
        refine (mem_zN G ϖ _).2 ⟨_, Subgroup.mem_inf.2 ⟨hyU, hK⟩, ?_⟩
        group
      have h : (QuotientGroup.mk (Quotient.out c) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        QuotientGroup.eq.2 (by simpa using inv_mem hin)
      exact (Quotient.out_eq c).symm.trans h
    exact hkill hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC hPJ V π r hrl x hx _ hfix
      (hni hcb hccB _ hyU hyK)
  · intro h
    exact absurd (Finset.mem_univ c1) h

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
section
noncomputable section

open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace UpperTheory.TNZ.ProductIrreducible₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_det_eq (u : kˣ) : ∃ g : GL (Fin 1) k, GeneralLinearGroup.det g = u := by
  refine ⟨⟨Matrix.diagonal fun _ => (u : k), Matrix.diagonal fun _ => ((u⁻¹ : kˣ) : k), ?_, ?_⟩, ?_⟩
  · simp [Matrix.diagonal_mul_diagonal]
  · simp [Matrix.diagonal_mul_diagonal]
  · ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem char_eq_of_equiv {μ μ' χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ (GL (Fin 1) k) W} (ψ : (detRep (Fin 1) μ').Equiv τ)
    (φ : (detRep (Fin 1) μ).Equiv (twist τ (detChar (Fin 1) χ))) (g : GL (Fin 1) k) :
    (μ (GeneralLinearGroup.det g) : ℂ) =
      (χ (GeneralLinearGroup.det g) : ℂ) * (μ' (GeneralLinearGroup.det g) : ℂ) := by
  have hτ : ∀ w : W, τ g w = (μ' (GeneralLinearGroup.det g) : ℂ) • w := by
    intro w
    obtain ⟨x, rfl⟩ := ψ.toLinearEquiv.surjective w
    have key : ψ.toLinearEquiv (detRep (Fin 1) μ' g x) = τ g (ψ.toLinearEquiv x) :=
      LinearMap.congr_fun (ψ.toIntertwiningMap.isIntertwining' g) x
    rw [← key]
    simp only [detRep, ofChar_apply, detChar_apply]
    rw [← smul_eq_mul, map_smul]
  have key : φ.toLinearEquiv (detRep (Fin 1) μ g 1) = twist τ (detChar (Fin 1) χ) g (φ.toLinearEquiv 1) :=
    LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) 1
  simp only [detRep, ofChar_apply, detChar_apply, twist_apply, hτ, mul_one, smul_smul] at key
  have hne : φ.toLinearEquiv 1 ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact one_ne_zero
  have h1 : φ.toLinearEquiv ((μ (GeneralLinearGroup.det g) : ℂ)) =
      (μ (GeneralLinearGroup.det g) : ℂ) • φ.toLinearEquiv 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h1] at key
  exact smul_left_injective ℂ hne key

theorem eq_on_units (y : IrrGL k) (h : 1 = y.1) (μ μ' : kˣ →* ℂˣ) (hμ : IsSmoothChar μ)
    (hs' : IsSmooth (detRep (Fin 1) μ')) (hi' : (detRep (Fin 1) μ').IsIrreducible)
    (hy : IrrGL.of (detRep (Fin 1) μ') hs' hi' = y) (j : ℤ)
    (hφ : Nonempty ((h ▸ GlobalTheory.SplitRead.Irr.ofDet 1 μ hμ : GlobalTheory.SplitRead.Irr k y.1).π.Equiv
      (twist (GlobalTheory.SplitRead.Irr.ofIrrRep y.2.rep).π (detChar (Fin y.1) (absPow k (j : ℂ))))))
    (u : kˣ) (hu : valuation k (u : k) = 1) : μ u = μ' u := by
  subst hy
  obtain ⟨φ⟩ := hφ
  obtain ⟨g, hg⟩ := exists_det_eq u
  have := char_eq_of_equiv (IrrGL.equivOf (detRep (Fin 1) μ') hs' hi') φ g
  rw [hg] at this
  have habs : (absPow k (j : ℂ) u : ℂ) = 1 := by
    rw [val_absPow, nabs_eq_one (k := k) hu]
    simp
  rw [habs, one_mul] at this
  exact Units.ext this

theorem product_irreducible_of_distinct_twists (hL : GlobalTheory.Mem.LiteralAutomorphy.LitLoc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)),
      (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) → ∀ η : Fin s → kˣ →* ℂˣ,
      (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      ∀ μ : ∀ b, Fin (d b) → kˣ →* ℂˣ,
      (∀ b j, IsSmoothChar (μ b j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ b j u = η b u) →
      (∀ b, IsCuspSupport (σ b) (fun _ => 1) (fun j => detRep (Fin 1) (μ b j))) →
        (multiProd (stdBlocks d hd) σ).IsIrreducible := by
  intro s
  induction s with
  | zero =>
    intros
    exact GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  | succ s ih =>
    intro N d hd X _ _ σ hs hi η hη μ hμ hcs
    have e : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨E⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hτi : (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ).IsIrreducible :=
      ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs _) (fun i => hi _)
        (fun i => η i.succ) (fun b c hbc => hη _ _ fun h => hbc (Fin.succ_injective _ h))
        (fun i => μ i.succ) (fun i => hμ _) (fun i => hcs _)
    have hτs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ) :=
      isSmooth_parInd _ _
    obtain ⟨h', x, hx, hxc⟩ := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel (d := fun i : Fin s => d i.succ) rfl
      (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => hasSupport_of_isCuspSupport (hcs i.succ)) hτi
    have hP := hL.disj k (d 0) (∑ i : Fin s, d i.succ) (d 0) h'
      { V := X 0, π := σ 0, smooth := hs 0, irr := hi 0 }
      { V := _, π := multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ, smooth := hτs,
        irr := hτi }
      (fun _ => 1) (fun b => (x b).1) (fun a => GlobalTheory.SplitRead.Irr.ofDet 1 (μ 0 a) (hμ 0 a).1)
      (fun b => GlobalTheory.SplitRead.Irr.ofIrrRep (x b).2.rep) (hcs 0) hxc ?_
    · exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hP
    · intro a b hab j _ hφ
      have hxb : x b ∈ ∑ i : Fin s, Finset.univ.val.map fun a =>
          IrrGL.of (detRep (Fin 1) (μ i.succ a)) ((hcs i.succ).2.1 a).2.2.1 ((hcs i.succ).2.1 a).2.1 := by
        rw [← hx]
        exact Multiset.mem_map_of_mem x (Finset.mem_univ_val b)
      obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hxb
      obtain ⟨j', -, hj'⟩ := Multiset.mem_map.1 hc
      obtain ⟨u, hu, hne⟩ := hη 0 c.succ (Fin.succ_ne_zero c).symm
      apply hne
      rw [← (hμ 0 a).2 u hu, ← (hμ c.succ j').2 u hu]
      exact eq_on_units (x b) hab (μ 0 a) (μ c.succ j') (hμ 0 a).1 _ _ hj' j hφ u hu

end UpperTheory.TNZ.ProductIrreducible₂

namespace UpperTheory.TNZ

theorem step_prodIrr : ProductIrreducibleProp := by
  unfold ProductIrreducibleProp
  intro hC hL k _ _ _ _ s N d hd X _ _ σ hs hi η hη hdv hne
  have H := fun b => hC hL k (d b) (X b) (σ b) (hs b) (hi b) (η b) (hη b) (hdv b)
  choose μ hμ hcs using H
  exact ProductIrreducible₂.product_irreducible_of_distinct_twists hL s N d hd X σ hs hi η hne μ hμ hcs

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarInertia
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Module
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne

namespace UpperTheory.TNZ.ScalarInertia

theorem eq_algebraMap_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : End ℂ V) (hs : f.IsSemisimple) (c : ℂ) (m : ℕ) (hc : f.charpoly = (X - C c) ^ m) :
    f = algebraMap ℂ (End ℂ V) c := by
  have hg : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hs
  have hn : IsNilpotent (f - algebraMap ℂ (End ℂ V) c) := by
    refine ⟨m, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa [map_pow, map_sub, aeval_X, aeval_C] using this
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hg)

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isSmooth_inv {ψ : Weil h →* ℂˣ} (hψ : IsSmooth ψ) : IsSmooth ψ⁻¹ :=
  hψ.of_le fun σ hσ => by simp [hσ]

variable [IsAlgClosure E Ω]

theorem unr_twist {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0)
    (m : ℕ) (hc : ∀ t : Ine (F := E) A,
      (a.ρ (ineIncl h t)).charpoly = (X - C ((ψ (ineIncl h t) : ℂˣ) : ℂ)) ^ m) :
    (a.twist ψ⁻¹ (isSmooth_inv hψ)).Unr := by
  refine ⟨hN, fun t => ?_⟩
  rw [WDRep.twist_ρ, eq_algebraMap_of_charpoly _ (a.semisimple _) _ _ (hc t),
    Algebra.algebraMap_eq_smul_one, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem iso_tensor {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0) :
    ((a.twist ψ⁻¹ (isSmooth_inv hψ)).tensor
      (WDRep.ofChars h (ι := Fin 1) (fun _ => ψ) fun _ => hψ)).Iso a := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ (Fin n → ℂ)), fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, WDRep.twist_ρ, WDRep.ofChars_ρ,
        LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul,
        LinearEquiv.funUnique_apply, Function.eval, diagEnd_apply, LinearMap.smul_apply, map_smul, smul_smul,
        MonoidHom.inv_apply]
      congr 1
      rw [mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp [hN]

end UpperTheory.TNZ.ScalarInertia

namespace UpperTheory.TNZ

open ScalarInertia in
theorem step_scalarInertia : ScalarOnInertiaProp := by
  intro E Ω _ _ _ _ _ A w h v ψ hψ hv hc
  obtain ⟨n, a, rfl⟩ := WD.exists_rep v
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hv
  simp only [WD.charPol_mk, WD.lpDim_mk] at hc
  refine ⟨WD.mk (a.twist ψ⁻¹ (isSmooth_inv hψ)), (WD.unr_mk _).mpr (unr_twist a ψ hψ hv _ hc), by simp, ?_⟩
  rw [WD.lpOfChar, WD.lpChar_mk]
  exact WD.sound (iso_tensor a ψ hψ hv).symm

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalOfUnramified
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_sphOfUnr : SphericalOfUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d v hv hd
  obtain ⟨⟨n, c⟩, rfl⟩ := H.bij.2 v
  have hn : n = d := by rw [← hd, H.dim]
  subst hn
  exact ⟨c.rep.V, inferInstance, inferInstance, c.rep.ρ, c.rep.smooth, c.rep.irr, (H.sph ⟨n, c⟩).2 hv,
    congrArg rc (IrrGL.of_rep ⟨n, c⟩)⟩

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalUnramified
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace SphericalUnramified

theorem isSpherical_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin d) k) V} {π : Representation ℂ (GL (Fin d) k) W} (e : ρ.Equiv π)
    (h : IsSpherical ρ) : IsSpherical π := by
  unfold IsSpherical IsSphericalFor at *
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, ?_⟩
  · intro g
    have hg := hx g
    have hint : e (ρ (g : GL (Fin d) k) x) = π (g : GL (Fin d) k) (e x) :=
      LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin d) k)) x
    rw [← hint, hg, map_smul]
  · intro h1
    apply h0
    have : e x = e 0 := by rw [h1, map_zero]
    exact EquivLike.injective e this

end SphericalUnramified

theorem step_sphUnr : SphericalUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL d X _ _ σ hs hi hsph
  exact (hL.sph (IrrGL.of σ hs hi)).1 (SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hsph)

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Uniformizer₂
section
noncomputable section

open ValuativeRel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Uniformizer₂

lemma algebraMap_ne_zero {w : 𝒪[k]} (hw : w ≠ 0) : algebraMap 𝒪[k] k w ≠ 0 := by
  intro h
  apply hw
  exact Subtype.ext (by simpa using h)

end Uniformizer₂

theorem step_unif : UniformizerProp (k := k) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  exact ⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.UnramifiedTwist
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace UnramifiedTwist

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have h1 := LinearMap.charpoly_sub_smul (c • (1 : Module.End ℂ V)) c
  rw [sub_self, LinearMap.charpoly_zero] at h1
  calc (c • (1 : Module.End ℂ V)).charpoly
      = ((c • (1 : Module.End ℂ V)).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [Polynomial.comp_assoc]; simp
    _ = (X - C c) ^ Module.finrank ℂ V := by rw [← h1, Polynomial.X_pow_comp]

theorem diagEnd_const (c : ℂ) :
    diagEnd (fun _ : Fin 1 => c) = c • (1 : Module.End ℂ (Fin 1 → ℂ)) :=
  LinearMap.ext fun v => funext fun i => by simp

end UnramifiedTwist

open UnramifiedTwist in
theorem step_unrTwist : UnramifiedTwistProp := by
  intro E Ω _ _ _ _ _ A w h u ψ hψ hu
  obtain ⟨n, a, rfl⟩ := WD.exists_rep u
  rw [WD.unr_mk] at hu
  obtain ⟨hN, hI⟩ := hu
  simp only [WD.lpOfChar, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.charPol_mk, WD.lpDim_mk]
  refine ⟨?_, fun t => ?_⟩
  · rw [WDRep.tensor_N, hN, WDRep.ofChars_N]
    simp
  · rw [WDRep.tensor_ρ, hI t, WDRep.ofChars_ρ, diagEnd_const, TensorProduct.map_smul_right,
      TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct]
    simp

end UpperTheory.TNZ
end
end

