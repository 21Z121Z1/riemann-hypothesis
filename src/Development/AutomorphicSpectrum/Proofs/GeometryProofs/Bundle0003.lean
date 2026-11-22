import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitWedge
section
namespace GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

theorem wedge_rows {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (z : Fin n → V) :
    exteriorPower.ιMulti K n (fun i => ∑ j, M i j • z j) = M.det • exteriorPower.ιMulti K n z := by
  have hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) =
      (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight
        (exteriorPower.ιMulti K n z) := by
    refine (Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
        (fun i => Pi.basisFun K (Fin n) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun hA M

theorem wedge_ne_zero {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent Ω v) : exteriorPower.ιMulti Ω n v ≠ 0 := by
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv
  let s := Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin n)).toOrderEmbedding
  have hs : exteriorPower.ιMulti_family Ω n v s = exteriorPower.ιMulti Ω n v := by
    simp only [exteriorPower.ιMulti_family, s, Equiv.symm_apply_apply]
    rfl
  exact hs ▸ hfam.ne_zero s

theorem exists_unit_wedge {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω)
    [IsLocalRing R] (A : Submodule R E) (p : ℕ) (ω : ⋀[Ω]^p E) (hω : ω ≠ 0)
    (H : Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} = Submodule.span R {ω}) :
    ∃ (b : Fin p → E) (r : R), (∀ i, b i ∈ A) ∧ IsUnit r ∧
      exteriorPower.ιMulti Ω p b = (r : Ω) • ω := by
  by_contra hcon
  push_neg at hcon
  let N : Submodule R (⋀[Ω]^p E) :=
    Submodule.map (LinearMap.toSpanSingleton R (⋀[Ω]^p E) ω) (IsLocalRing.maximalIdeal R)
  have hle : Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨b, hb, rfl⟩
    have hmem : exteriorPower.ιMulti Ω p b ∈ Submodule.span R {ω} :=
      H ▸ Submodule.subset_span ⟨b, hb, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
    have hnu : ¬ IsUnit r := fun hu => hcon b r hb hu hr.symm
    exact ⟨r, (IsLocalRing.mem_maximalIdeal r).2 hnu, by simpa using hr⟩
  have hωN : ω ∈ N := hle (H ▸ Submodule.mem_span_singleton_self ω)
  obtain ⟨r, hr, hrω⟩ := hωN
  have hrω' : (r : Ω) • ω = ω := hrω
  have h1 : (r : Ω) = 1 := by
    have h0 : ((r : Ω) - 1) • ω = 0 := by rw [sub_smul, one_smul, hrω', sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hω
  have hr1 : r = 1 := Subtype.ext h1
  rw [hr1] at hr
  exact ((IsLocalRing.mem_maximalIdeal (1 : R)).1 hr) isUnit_one

theorem wedge_update_sum {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {p : ℕ}
    (b : Fin p → E) (c : Fin p → Ω) (j : Fin p) :
    exteriorPower.ιMulti Ω p (Function.update b j (∑ k, c k • b k)) =
      c j • exteriorPower.ιMulti Ω p b := by
  rw [AlternatingMap.map_update_sum, Finset.sum_eq_single j]
  · rw [AlternatingMap.map_update_smul, Function.update_eq_self]
  · intro k _ hk
    rw [AlternatingMap.map_update_smul, AlternatingMap.map_update_self _ _ hk.symm, smul_zero]
  · simp

theorem wedge_frame : ∀ (Ω E : Type) [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω)
    [IsLocalRing R] (A : Submodule R E) (p : ℕ) (v : Fin p → E) (α : Ω),
    LinearIndependent Ω v → (∀ y ∈ A, y ∈ Submodule.span Ω (Set.range v)) → α ≠ 0 →
    Submodule.span R {w : ⋀[Ω]^p E | ∃ b : Fin p → E, (∀ i, b i ∈ A) ∧
      w = exteriorPower.ιMulti Ω p b} = Submodule.span R {α • exteriorPower.ιMulti Ω p v} →
    ∃ P : Matrix (Fin p) (Fin p) Ω, LinearIndependent Ω (fun i => ∑ j, P i j • v j) ∧
      A = Submodule.span R (Set.range fun i => ∑ j, P i j • v j) ∧
      ∃ c : Ω, c ∈ R ∧ c⁻¹ ∈ R ∧ c ≠ 0 ∧ P.det = c * α := by
  intro Ω E _ _ _ R _ A p v α hv hA hα H
  have hιv := wedge_ne_zero v hv
  have hω : α • exteriorPower.ιMulti Ω p v ≠ 0 := smul_ne_zero hα hιv
  obtain ⟨b, r, hb, hu, hιb⟩ := exists_unit_wedge R A p _ hω H
  obtain ⟨u, rfl⟩ := hu
  have hc0 : ((u : R) : Ω) ≠ 0 := by
    intro h0
    exact u.ne_zero (Subtype.ext h0)
  have hcinv : ((u : R) : Ω)⁻¹ = (((u⁻¹ : Rˣ) : R) : Ω) := by
    have h : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hιb0 : exteriorPower.ιMulti Ω p b ≠ 0 := by
    rw [hιb]; exact smul_ne_zero hc0 hω
  have hbli : LinearIndependent Ω b := by
    by_contra hnot
    exact hιb0 (AlternatingMap.map_linearDependent _ _ hnot)
  have hex : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hA _ (hb i))
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin p) (Fin p) Ω, ∀ i, ∑ j, P i j • v j = b i :=
    ⟨Matrix.of fun i => (hex i).choose, fun i => (hex i).choose_spec⟩
  have hPb : (fun i => ∑ j, P i j • v j) = b := funext hP
  have hdet : P.det = ((u : R) : Ω) * α := by
    have h1 := wedge_rows P v
    rw [hPb, hιb, smul_smul] at h1
    exact (smul_left_injective Ω hιv h1).symm
  refine ⟨P, ?_, ?_, (u : R), (u : R).2, hcinv ▸ ((u⁻¹ : Rˣ) : R).2, hc0, hdet⟩
  · rw [hPb]; exact hbli
  · rw [hPb]
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · intro y hy
      have hspan : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range v) := by
        haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range v)) :=
          FiniteDimensional.span_of_finite Ω (Set.finite_range v)
        refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
        · rintro _ ⟨i, rfl⟩
          exact hA _ (hb i)
        · rw [finrank_span_eq_card hbli, finrank_span_eq_card hv]
      have hy' : y ∈ Submodule.span Ω (Set.range b) := hspan ▸ hA y hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hy'
      have hcR : ∀ j, c j ∈ R := by
        intro j
        have hmem : exteriorPower.ιMulti Ω p (Function.update b j y) ∈
            Submodule.span R {α • exteriorPower.ιMulti Ω p v} := by
          rw [← H]
          refine Submodule.subset_span ⟨_, fun i => ?_, rfl⟩
          by_cases hij : i = j
          · subst hij; simpa using hy
          · simpa [Function.update_of_ne hij] using hb i
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
        rw [← hc, wedge_update_sum, hιb] at hs
        have hs' : (s : Ω) • (α • exteriorPower.ιMulti Ω p v) =
            (c j * ((u : R) : Ω)) • (α • exteriorPower.ιMulti Ω p v) := by
          rw [mul_smul]; exact hs
        have hsc : (s : Ω) = c j * ((u : R) : Ω) := smul_left_injective Ω hω hs'
        have hcj : c j = (s : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) := by
          rw [← hcinv, hsc, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
        rw [hcj]
        exact R.mul_mem s.2 ((u⁻¹ : Rˣ) : R).2
      rw [← hc]
      refine Submodule.sum_mem _ fun j _ => ?_
      have : c j • b j = (⟨c j, hcR j⟩ : R) • b j := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨i, rfl⟩
      exact hb i

end GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsValuationSubringExtension
section
open Polynomial IsLocalRing

namespace GlobalTheory.CompanionTheory.Chevalley

variable {Ω L : Type*} [Field Ω] [Field L]

def Functional (G : Subring (Ω × L)) : Prop := ∀ l : L, ((0 : Ω), l) ∈ G → l = 0

theorem exists_maximal_functional (G₀ : Subring (Ω × L)) (h₀ : Functional G₀) :
    ∃ G, G₀ ≤ G ∧ Maximal Functional G := by
  have hub : ∀ c ⊆ {G : Subring (Ω × L) | Functional G}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {G : Subring (Ω × L) | Functional G}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hch y hy
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    show Functional (sSup c)
    intro l hl
    obtain ⟨s, hs, hls⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).mp hl
    exact (hc hs : Functional s) l hls
  obtain ⟨m, hm, hmax⟩ := zorn_le_nonempty₀ _ hub G₀ h₀
  exact ⟨m, hm, hmax⟩

def saturation (G : Subring (Ω × L)) (t : Ω × L) (ht : t ∈ G) : Subring (Ω × L) where
  carrier := {u | ∃ n : ℕ, t ^ n * u ∈ G}
  mul_mem' := by
    rintro u v ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := G.mul_mem hn hm
    convert this using 1
    ring
  one_mem' := ⟨0, by simpa using G.one_mem⟩
  add_mem' := by
    rintro u v ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := G.add_mem (G.mul_mem (G.pow_mem ht m) hn) (G.mul_mem (G.pow_mem ht n) hm)
    convert this using 1
    ring
  zero_mem' := ⟨0, by simp [G.zero_mem]⟩
  neg_mem' := by
    rintro u ⟨n, hn⟩
    exact ⟨n, by simpa using G.neg_mem hn⟩

theorem inv_mem {G : Subring (Ω × L)} (hG : Maximal Functional G) {b : Ω} {l : L}
    (hb : (b, l) ∈ G) (hl : l ≠ 0) : (b⁻¹, l⁻¹) ∈ G := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hl (hG.1 l hb)
  have hmem : ∀ u, u ∈ saturation G (b, l) hb ↔ ∃ n : ℕ, (b, l) ^ n * u ∈ G := fun u => Iff.rfl
  have hS : Functional (saturation G (b, l) hb) := by
    intro m hm
    obtain ⟨n, hn⟩ := (hmem _).mp hm
    rw [Prod.pow_mk, Prod.mk_mul_mk, mul_zero] at hn
    have h0 := hG.1 _ hn
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero n hl)
  have hle : G ≤ saturation G (b, l) hb := fun u hu => (hmem u).mpr ⟨0, by simpa using hu⟩
  apply hG.2 hS hle
  refine (hmem _).mpr ⟨1, ?_⟩
  rw [pow_one, Prod.mk_mul_mk, mul_inv_cancel₀ hb0, mul_inv_cancel₀ hl]
  exact G.one_mem

def p₁ (G : Subring (Ω × L)) : G →+* Ω := (RingHom.fst Ω L).comp G.subtype

def p₂ (G : Subring (Ω × L)) : G →+* L := (RingHom.snd Ω L).comp G.subtype

theorem isUnit_of_p₂_ne_zero {G : Subring (Ω × L)} (hG : Maximal Functional G) (r : G)
    (h : p₂ G r ≠ 0) : IsUnit r := by
  obtain ⟨⟨b, l⟩, hr⟩ := r
  have hl : l ≠ 0 := h
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hl (hG.1 l hr)
  have hinv := inv_mem hG hr hl
  have hprod : (⟨(b, l), hr⟩ : G) * ⟨(b⁻¹, l⁻¹), hinv⟩ = 1 := by
    apply Subtype.ext
    simp [hb0, hl]
  exact ⟨⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩, rfl⟩

theorem isLocalRing_of_maximal {G : Subring (Ω × L)} (hG : Maximal Functional G) :
    IsLocalRing G := by
  have : Nontrivial G := (p₂ G).domain_nontrivial
  have key : ∀ r : G, r ∈ nonunits G ↔ p₂ G r = 0 := by
    intro r
    rw [mem_nonunits_iff]
    constructor
    · intro hr
      by_contra h
      exact hr (isUnit_of_p₂_ne_zero hG r h)
    · intro h hu
      have := hu.map (p₂ G)
      rw [h] at this
      exact not_isUnit_zero this
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [key] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

theorem exists_common_root [IsAlgClosed L] {k : Type*} [Field k] (ι : k →+* L) (I : Ideal k[X])
    (hI : I ≠ ⊤) : ∃ ξ : L, ∀ p ∈ I, eval₂ ι ξ p = 0 := by
  classical
  have hmem : ∀ p, p ∈ I ↔ Submodule.IsPrincipal.generator I ∣ p :=
    fun p => Submodule.IsPrincipal.mem_iff_generator_dvd I
  by_cases hf0 : Submodule.IsPrincipal.generator I = 0
  · refine ⟨0, fun p hp => ?_⟩
    rw [hmem, hf0, zero_dvd_iff] at hp
    rw [hp, eval₂_zero]
  · have hnu : ¬ IsUnit (Submodule.IsPrincipal.generator I) := by
      intro hu
      apply hI
      rw [Ideal.eq_top_iff_one, hmem]
      exact hu.dvd
    have hdeg : (Submodule.IsPrincipal.generator I).degree ≠ 0 := by
      intro h
      exact hnu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_eval₂_eq_zero ι _ hdeg
    refine ⟨ξ, fun p hp => ?_⟩
    obtain ⟨q, rfl⟩ := (hmem p).mp hp
    rw [eval₂_mul, hξ, zero_mul]

theorem mem_of_relations {G : Subring (Ω × L)} (hG : Maximal Functional G) (x : Ω) (ξ : L)
    (h : ∀ p : Polynomial G, eval₂ (p₁ G) x p = 0 → eval₂ (p₂ G) ξ p = 0) : (x, ξ) ∈ G := by
  have hfst : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).1 = eval₂ (p₁ G) x p :=
    fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.fst Ω L) (x, ξ)
  have hsnd : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).2 = eval₂ (p₂ G) ξ p :=
    fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.snd Ω L) (x, ξ)
  have hS : Functional (Polynomial.eval₂RingHom G.subtype (x, ξ)).range := by
    intro l hl
    obtain ⟨p, hp⟩ := RingHom.mem_range.mp hl
    have hp' : eval₂ G.subtype (x, ξ) p = (0, l) := hp
    have h1 : eval₂ (p₁ G) x p = 0 := by
      have := hfst p
      rw [hp'] at this
      exact this.symm
    have h2 := h p h1
    have := hsnd p
    rw [hp'] at this
    exact this.trans h2
  have hle : G ≤ (Polynomial.eval₂RingHom G.subtype (x, ξ)).range := by
    intro t ht
    exact RingHom.mem_range.mpr ⟨C ⟨t, ht⟩, by simp⟩
  exact hG.2 hS hle (RingHom.mem_range.mpr ⟨X, by simp⟩)

theorem exists_mem_of_dominates [IsAlgClosed L] {G : Subring (Ω × L)} (hG : Maximal Functional G)
    [IsLocalRing G] [IsLocalHom (p₂ G)] (V : ValuationSubring Ω) (g : G →+* V)
    (hg : ∀ r, (g r : Ω) = p₁ G r) [IsLocalHom g] (x : V) : ∃ ξ : L, ((x : Ω), ξ) ∈ G := by
  classical
  have hsurj : Function.Surjective (Polynomial.mapRingHom (IsLocalRing.residue G)) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective
  have hJ : Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G))
      (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))) ≠ ⊤ := by
    intro hJ
    have h1 : (1 : Polynomial (IsLocalRing.ResidueField G)) ∈ Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G))
        (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))) := by
      rw [hJ]
      exact Submodule.mem_top
    obtain ⟨p, hpI, hp1'⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h1
    have hp : eval₂ (p₁ G) (x : Ω) p = 0 := by
      rw [RingHom.mem_ker, Polynomial.coe_eval₂RingHom] at hpI
      exact hpI
    have hp1 : Polynomial.map (IsLocalRing.residue G) p = 1 := hp1'
    have hcomp : V.subtype.comp g = p₁ G := RingHom.ext hg
    have h0 : eval₂ g x p = 0 := by
      apply Subtype.val_injective
      have := Polynomial.hom_eval₂ p g V.subtype x
      rw [hcomp] at this
      exact this.trans hp
    have hc : (IsLocalRing.residue V).comp g
        = (IsLocalRing.ResidueField.map g).comp (IsLocalRing.residue G) := by
      ext r
      simp
    have h2 : IsLocalRing.residue V (eval₂ g x p) = 1 := by
      rw [Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map, hp1, eval₂_one]
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  obtain ⟨ξ, hξ⟩ := exists_common_root (IsLocalRing.ResidueField.lift (p₂ G)) _ hJ
  refine ⟨ξ, mem_of_relations hG (x : Ω) ξ fun p hp => ?_⟩
  have hpI : p ∈ RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω)) := by
    rw [RingHom.mem_ker, Polynomial.coe_eval₂RingHom]
    exact hp
  have := hξ _ (Ideal.mem_map_of_mem _ hpI)
  rw [Polynomial.coe_mapRingHom, Polynomial.eval₂_map, IsLocalRing.ResidueField.lift_comp_residue] at this
  exact this

theorem exists_valuationSubring_extension [IsAlgClosed L] (A : Subring Ω) (φ : A →+* L) :
    ∃ (V : ValuationSubring Ω) (hAV : ∀ a ∈ A, a ∈ V) (ψ : V →+* L),
      ∀ a : A, ψ ⟨a.1, hAV a.1 a.2⟩ = φ a := by
  classical
  have hG₀f : Functional (A.subtype.prod φ).range := by
    intro l hl
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp hl
    have h1 : (a : Ω) = 0 := congrArg Prod.fst ha
    have h2 : φ a = l := congrArg Prod.snd ha
    have ha0 : a = 0 := Subtype.ext h1
    rw [← h2, ha0, map_zero]
  obtain ⟨G, hG₀G, hG⟩ := exists_maximal_functional _ hG₀f
  have : IsLocalRing G := isLocalRing_of_maximal hG
  have : IsLocalHom (p₂ G) := ⟨fun r hr => isUnit_of_p₂_ne_zero hG r hr.ne_zero⟩
  have hinj : Function.Injective (p₁ G) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨b, l⟩, hr⟩ h0
    have hb : b = 0 := h0
    subst hb
    have hl := hG.1 l hr
    subst hl
    rfl
  let e : G ≃+* (p₁ G).range := RingEquiv.ofBijective (p₁ G).rangeRestrict
    ⟨fun r s h => hinj (congrArg Subtype.val h), (p₁ G).rangeRestrict_surjective⟩
  have : IsLocalRing (p₁ G).range :=
    IsLocalRing.of_surjective' (p₁ G).rangeRestrict (p₁ G).rangeRestrict_surjective
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.mk (p₁ G).range)
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  have : IsLocalHom (p₁ G).rangeRestrict :=
    IsLocalHom.of_surjective _ (p₁ G).rangeRestrict_surjective
  let g : G →+* V := (Subring.inclusion hle).comp (p₁ G).rangeRestrict
  have : IsLocalHom g := ⟨fun r hr => IsLocalHom.map_nonunit (f := (p₁ G).rangeRestrict) r
    (IsLocalHom.map_nonunit (f := Subring.inclusion hle) (self := hloc) ((p₁ G).rangeRestrict r) hr)⟩
  have hVle : ∀ x ∈ V, x ∈ (p₁ G).range := by
    intro x hx
    obtain ⟨ξ, hξ⟩ := exists_mem_of_dominates hG V g (fun r => rfl) ⟨x, hx⟩
    exact RingHom.mem_range.mpr ⟨⟨(x, ξ), hξ⟩, rfl⟩
  have hVle' : V.toSubring ≤ (p₁ G).range := fun x hx => hVle x hx
  have hmem0 : ∀ a : A, ((a : Ω), φ a) ∈ G := fun a => hG₀G (RingHom.mem_range.mpr ⟨a, rfl⟩)
  have hAV : ∀ a ∈ A, a ∈ V := fun a ha =>
    hle (RingHom.mem_range.mpr ⟨⟨(a, φ ⟨a, ha⟩), hmem0 ⟨a, ha⟩⟩, rfl⟩)
  let ψ : V →+* L := (p₂ G).comp (e.symm.toRingHom.comp (Subring.inclusion hVle'))
  refine ⟨V, hAV, ψ, fun a => ?_⟩
  have key : e ⟨((a : Ω), φ a), hmem0 a⟩ = Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩ := Subtype.ext rfl
  have hpre : e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩) = ⟨((a : Ω), φ a), hmem0 a⟩ := by
    rw [← key, RingEquiv.symm_apply_apply]
  show p₂ G (e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩)) = φ a
  rw [hpre]
  rfl

theorem chevalley_extension : ∀ (Ω L : Type) [Field Ω] [Field L] [IsAlgClosed L] (A : Subring Ω)
    (φ : A →+* L), ∃ (V : ValuationSubring Ω) (hAV : ∀ a ∈ A, a ∈ V) (ψ : V →+* L),
      ∀ a : A, ψ ⟨a.1, hAV a.1 a.2⟩ = φ a := by
  intro Ω L _ _ _ A φ
  exact exists_valuationSubring_extension A φ

end GlobalTheory.CompanionTheory.Chevalley
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GapN
section
namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

def gapN {Ψ : Type} {N : ℕ} (ν : Ψ × Fin N → ℤ) : Option (Ψ × Fin N) → ℤ
  | none => 0
  | some p => ν p - if h : (p.2 : ℕ) + 1 < N then ν (p.1, ⟨p.2 + 1, h⟩) else 0

end GlobalTheory.CompanionTheory.Ar.ExRefEff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HBBound
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hB_bound : ∀ (N j B : ℕ) (S : Finset ℕ) (d v : ℕ → ℝ) (lrd Lv hrec hB : ℝ), j ≤ N → 3 ≤ B → 0 ≤ lrd → |hrec| ≤ N * (3 / 2 * lrd + |Lv| / 2) → hB = hrec + ∑ p ∈ S, d p → (∀ p ∈ S, p.Prime) → (∀ p ∈ S, 0 ≤ v p) → (∀ p ∈ S, |d p| ≤ (N / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p) → ∑ p ∈ S, v p * Real.log p ≤ lrd → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 → |hB| ≤ 4 * N * (Real.log B + lrd + |Lv|) := by
  intro N j B S d v lrd Lv hrec hB hj hB3 hl hrecb hBeq hprime hv hd hsv hsl
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogB : 1 ≤ Real.log B := by
    have h3 : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    have hexp : Real.exp 1 ≤ B := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hsum : |∑ p ∈ S, d p| ≤ N * (3 * Real.log B + 1) + N * lrd := by
    calc |∑ p ∈ S, d p| ≤ ∑ p ∈ S, |d p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, ((N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hdp := hd p hp
        have e : ((N : ℝ) / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p =
            (N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p) := by ring
        linarith
      _ = (N : ℝ) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) + N * ∑ p ∈ S, v p * Real.log p := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ N * (3 * Real.log B + 1) + N * lrd := by gcongr
  have htot : |hB| ≤ |hrec| + |∑ p ∈ S, d p| := by
    rw [hBeq]; exact abs_add_le _ _
  nlinarith [mul_nonneg hN (sub_nonneg.mpr hlogB), mul_nonneg hN hl, mul_nonneg hN (abs_nonneg Lv)]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitRootAnalytic
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.SimpleRoot

theorem exists_analytic_simple_root
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ)
    (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) w₀)
    (h0 : ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0)
    (h1 : ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0) :
    ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧
      AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W,
        ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  set F : E × ℂ → ℂ := fun p => ∑ j ∈ Finset.range (n + 1), c j p.1 * p.2 ^ j with hFdef
  have hFa : AnalyticAt ℂ F (w₀, τ₀) := by
    refine Finset.analyticAt_fun_sum _ fun j _ => ?_
    exact ((hc j).comp analyticAt_fst).mul (analyticAt_snd.pow j)
  have cdf : ContDiffAt ℂ (⊤ : WithTop ℕ∞) F (w₀, τ₀) := hFa.contDiffAt
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set d : ℂ := ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) with hd_def
  have hd : HasDerivAt (fun τ => F (w₀, τ)) d τ₀ :=
    HasDerivAt.fun_sum (u := Finset.range (n + 1)) (A := fun j τ => c j w₀ * τ ^ j)
      (A' := fun j => (j : ℂ) * c j w₀ * τ₀ ^ (j - 1)) fun j _ => by
        rw [show (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) = c j w₀ * ((j : ℂ) * τ₀ ^ (j - 1)) by ring]
        exact (hasDerivAt_pow j τ₀).const_mul (c j w₀)
  have hfd : HasFDerivAt (fun τ => F (w₀, τ))
      ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)) τ₀ :=
    hFa.differentiableAt.hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_right w₀ τ₀)
  have heq : (fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d :=
    hfd.unique hd.hasFDerivAt
  have if₂ : ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d h1), ?_⟩
    ext
    simp
  set g := cdf.implicitFunction pn if₂ with hg_def
  have hg : AnalyticAt ℂ g w₀ := (cdf.contDiffAt_implicitFunction pn if₂).analyticAt
  obtain ⟨V₂, W, hV₂o, hw₀V₂, hWo, hτ₀W, hsub⟩ :=
    mem_nhds_prod_iff'.1 (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  refine ⟨{w | AnalyticAt ℂ g w} ∩ V₂, W, g, (isOpen_analyticAt ℂ g).inter hV₂o, ⟨hg, hw₀V₂⟩, hWo, hτ₀W,
    fun w hw => hw.1, ?_⟩
  intro w hw τ hτ hroot
  have hmem := hsub (Set.mk_mem_prod hw.2 hτ)
  simp only [Set.mem_ofPred_eq] at hmem
  have h' : F (w, τ) = F (w₀, τ₀) := by
    change (∑ j ∈ Finset.range (n + 1), c j w * τ ^ j) = ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j
    rw [hroot, h0]
  exact (hmem.1 h').symm

end GlobalTheory.CompanionTheory.SimpleRoot
end

