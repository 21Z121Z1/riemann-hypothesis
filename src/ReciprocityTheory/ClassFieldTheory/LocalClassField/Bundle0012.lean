import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0002
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0009
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0007
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0003
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0005
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0006
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Bundle0003

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.CyclicBr
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

@[reducible] def commGroupOfZpowers {G : Type*} [inst : Group G] (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    CommGroup G :=
  { inst with
    mul_comm := fun a b => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
      rw [← zpow_add, ← zpow_add, add_comm] }

theorem nonempty_H_odd {R G : Type} [CommRing R] [Group G] [Fintype G] [TopologicalSpace G]
    [IsTopologicalGroup G] [DiscreteTopology G] (M : TRep R G) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃+ Herbrand.H1 M.rho g₀) := by
  let _ : CommGroup G := commGroupOfZpowers g₀ hg
  obtain ⟨e⟩ := Herbrand.nonempty_groupCohomology_odd M.rho g₀ hg i hi
  exact ⟨(finEquiv M i).toAddEquiv.trans e⟩

theorem nonempty_H_even {R G : Type} [CommRing R] [Group G] [Fintype G] [TopologicalSpace G]
    [IsTopologicalGroup G] [DiscreteTopology G] (M : TRep R G) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (i : ℕ) (h0 : i ≠ 0)
    (hi : Even i) : Nonempty (M.H i ≃+ Herbrand.TateZerothCohomology M.rho g₀) := by
  let _ : CommGroup G := commGroupOfZpowers g₀ hg
  obtain ⟨e⟩ := Herbrand.nonempty_groupCohomology_even M.rho g₀ hg i h0 hi
  exact ⟨(finEquiv M i).toAddEquiv.trans e⟩

theorem herbrand_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Herbrand.HFin (layer p K L).rho g₀ ∧ Herbrand.h (layer p K L).rho g₀ = degLK p K L := by
  have he : 0 < eK p L := eK_pos p L hL
  obtain ⟨hU, hU1⟩ := herbrand_layerU hK hL h g₀ hg
  obtain ⟨hZ, -, -, hZ1⟩ := Herbrand.h_int (trivRep (GalLK p K L) ℤ).rho (fun _ _ => rfl) g₀
  obtain ⟨h1, h2⟩ := Herbrand.h_mul (layerU p K L).rho (layer p K L).rho (trivRep (GalLK p K L) ℤ).rho g₀
    (layerUIncl p K L).u.toAddMonoidHom (vLayer p K L).u.toAddMonoidHom (layerUIncl_injective p)
    (fun x => by
      have := ker_vLayer p he h
      exact (LinearMap.mem_ker.symm.trans (by rw [this])).trans LinearMap.mem_range)
    (vLayer_surjective p he h) (fun c a => (layerUIncl p K L).equiv c a)
    (fun c b => (vLayer p K L).equiv c b) hU hZ
  refine ⟨h1, ?_⟩
  rw [h2, hU1, one_mul]
  exact hZ1

theorem subsingleton_h1_cyclic_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : Subsingleton (Herbrand.H1 (layer p K L).rho g₀) := by
  have h1 : Subsingleton ((layer p K L).H 1) :=
    quotient_multiplicative_h1_subsingleton p K (subG p K L) (layer p K L) (layerInf p K L)
      (InflationRestrictionInvariants.invariants_isInvRep (kbarT p K) (subG p K L))
  have hS := totallySeparatedSpace_GalLK p K L
  have hT2 : T2Space (GalLK p K L) := TotallySeparatedSpace.t2Space
  have hT : T1Space (GalLK p K L) := T2Space.t1Space
  have hF : Finite (GalLK p K L) := Finite.of_fintype _
  have hD : DiscreteTopology (GalLK p K L) := Finite.instDiscreteTopology
  obtain ⟨e⟩ := nonempty_H_odd (layer p K L) g₀ hg 1 odd_one
  exact e.symm.toEquiv.subsingleton

theorem card_H0hat_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card (Herbrand.TateZerothCohomology (layer p K L).rho g₀) = degLK p K L := by
  have := subsingleton_h1_cyclic_layer h g₀ hg
  have h1 := (herbrand_layer hK hL h g₀ hg).2
  rw [Herbrand.h_eq_card_H0hat] at h1
  exact_mod_cast h1

theorem card_h2_cyclic_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card ((layer p K L).H 2) = degLK p K L := by
  have := finite_GalLK (K := K) hL
  have hD : DiscreteTopology (GalLK p K L) := discreteTopology_GalLK hL
  let _ : Fintype (GalLK p K L) := Fintype.ofFinite _
  obtain ⟨e⟩ := nonempty_H_even (layer p K L) g₀ hg 2 two_ne_zero even_two
  rw [Nat.card_congr e.toEquiv, card_H0hat_layer hK hL h g₀ hg]

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.EulerDefs
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Euler

open _root_.Neutral.B1

noncomputable section

section Q

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

def qEd (p d : ℕ) (rho : Representation R G M) : ℚ :=
  ((Nat.card (H0 rho) : ℚ) * (Nat.card (H2 rho) : ℚ) * (p : ℚ) ^ (d * padicValNat p (Nat.card M))) /
    (Nat.card (H1 rho) : ℚ)

def SimpleRep (rho : Representation R G M) : Prop :=
  Nontrivial M ∧ ∀ S : Submodule R M, (∀ g, ∀ m ∈ S, rho g m ∈ S) → S = ⊥ ∨ S = ⊤

def fnRep (rho : Representation R G M) (U : Subgroup G) : Representation R G (G ⧸ U → M) where
  toFun g :=
    { toFun := fun F x => rho g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (rho g) _ _
      map_smul' := fun c F => funext fun x => map_smul (rho g) _ _ }
  map_one' := LinearMap.ext fun F => funext fun x => by
    show rho 1 (F ((1 : G)⁻¹ • x)) = F x
    rw [inv_one, one_smul, map_one]; rfl
  map_mul' g h := LinearMap.ext fun F => funext fun x => by
    show rho (g * h) (F ((g * h)⁻¹ • x)) = rho g (rho h (F (h⁻¹ • g⁻¹ • x)))
    rw [mul_inv_rev, mul_smul, map_mul]; rfl

def intRep (rho : Representation R G M) : Representation ℤ G M where
  toFun g := (rho g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun m => by
    show rho 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show rho (g * h) m = rho g (rho h m)
    rw [map_mul]; rfl

end Q

def qE (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R (GK p K) M) : ℚ :=
  qEd p (Module.finrank ℚ_[p] K) rho

section ZG

variable (G : Type) [Group G]

abbrev ZG : Type := MonoidAlgebra ℤ G

variable {G} (l : ℕ) (D A : Type) [AddCommGroup D] [Module (ZG G) D] [AddCommGroup A] [Module (ZG G) A]

def mulL : A →ₗ[ZG G] A := l • LinearMap.id

abbrev modL : Type := A ⧸ LinearMap.range (mulL (G := G) l A)

abbrev torL : Submodule (ZG G) A := LinearMap.ker (mulL (G := G) l A)

def eps : ℚ := (Nat.card (D →ₗ[ZG G] modL (G := G) l A) : ℚ) / (Nat.card (D →ₗ[ZG G] torL (G := G) l A) : ℚ)

variable (G) in

def fixG : Type := {d : D // ∀ g : G, MonoidAlgebra.of ℤ G g • d = d}

end ZG

section Hom

variable (N : Type) [Group N] [TopologicalSpace N] (M : Type) [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]

def homSub : AddSubgroup (N → M) where
  carrier := {f | Continuous f ∧ ∀ a b, f (a * b) = f a + f b}
  zero_mem' := ⟨continuous_const, fun _ _ => (add_zero (0 : M)).symm⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun a b => by
    show f (a * b) + f' (a * b) = f a + f' a + (f b + f' b)
    rw [hf.2, hf'.2]; abel⟩
  neg_mem' := fun {f} hf => ⟨hf.1.neg, fun a b => by
    show - f (a * b) = - f a + - f b
    rw [hf.2]; abel⟩

end Hom

def conjN {G : Type} [Group G] (N : Subgroup G) [hN : N.Normal] (s : G) (g : N) : N :=
  ⟨s⁻¹ * g * s, by simpa using hN.conj_mem g.1 g.2 s⁻¹⟩

section OL

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def OLadd : AddSubgroup (PadicAlgCl p) where
  carrier := {x | x ∈ L ∧ ‖x‖ ≤ 1}
  zero_mem' := ⟨L.zero_mem, by simp⟩
  add_mem' := fun {x y} hx hy => ⟨L.add_mem hx.1 hy.1,
    (PadicAlgCl.isNonarchimedean p x y).trans (max_le hx.2 hy.2)⟩
  neg_mem' := fun {x} hx => ⟨L.neg_mem hx.1, by rw [norm_neg]; exact hx.2⟩

variable {p K L}

def integerRingGaloisAction (hKL : K ≤ L) [hN : (subG p K L).Normal] : Representation ℤ (GK p K) (OLadd p L) where
  toFun σ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => ⟨σ x.1, (subG_normal_iff hKL).1 hN σ x.1 x.2.1, by rw [norm_map_GK]; exact x.2.2⟩
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }
  map_one' := rfl
  map_mul' _ _ := rfl

def OLrep (hKL : K ≤ L) [(subG p K L).Normal] : Representation ℤ (GalLK p K L) (OLadd p L) :=
  QuotientGroup.lift (subG p K L) (integerRingGaloisAction hKL) fun _ hσ =>
    LinearMap.ext fun x => Subtype.ext (hσ x.1 x.2.1)

end OL

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Euler
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenB
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem norm_coe_K (x : K) : ‖(x : PadicAlgCl p)‖ = ‖x‖ := rfl

theorem UK_eq_preimage : (UK p K : Set Kˣ) = Units.val ⁻¹' Metric.sphere (0 : K) 1 := by
  ext x
  simp only [Set.mem_preimage, mem_sphere_zero_iff_norm]
  rfl

theorem image_UK : Units.val '' (UK p K : Set Kˣ) = Metric.sphere (0 : K) 1 := by
  rw [UK_eq_preimage, Set.image_preimage_eq_iff]
  intro x hx
  have hx' : ‖x‖ = 1 := by simpa using hx
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at hx'
  exact ⟨Units.mk0 x h0, rfl⟩

theorem isCompact_UK' (hK : FiniteDimensional ℚ_[p] K) : IsCompact (UK p K : Set Kˣ) := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  rw [Units.isEmbedding_val₀.isCompact_iff, image_UK]
  exact isCompact_sphere _ _

theorem mem_UK_of_norm_sub_one_lt (x : Kˣ) (hx : ‖(x : K) - 1‖ < 1) : x ∈ UK p K := by
  show ‖((x : K) : PadicAlgCl p)‖ = 1
  rw [norm_coe_K]
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (x : K) - 1) (y := 1)
    (by rw [norm_one]; exact hx.ne)
  rw [sub_add_cancel, norm_one, max_eq_right hx.le] at h
  exact h

theorem mem_nhds_one_iff (S : Set Kˣ) :
    S ∈ nhds (1 : Kˣ) ↔ ∃ ε > 0, ∀ x : Kˣ, ‖(x : K) - 1‖ < ε → x ∈ S := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap, Units.val_one]
  constructor
  · rintro ⟨t, ht, hts⟩
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 ht
    refine ⟨ε, hε, fun x hx => hts (hb ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]; exact hx
  · rintro ⟨ε, hε, h⟩
    refine ⟨Metric.ball 1 ε, Metric.ball_mem_nhds _ hε, fun x hx => h x ?_⟩
    have : (x : K) ∈ Metric.ball (1 : K) ε := hx
    rwa [Metric.mem_ball, dist_eq_norm] at this

theorem isOpen_UKi (i : ℕ) : IsOpen (UKi p K i : Set Kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  rw [mem_nhds_one_iff]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨min 1 ((p : ℝ) ^ (- (i : ℝ) / eK p K)), lt_min one_pos (Real.rpow_pos_of_pos hp _), fun x hx => ?_⟩
  exact (mem_UKi_iff p K i x).2 ⟨mem_UK_of_norm_sub_one_lt x (hx.trans_le (min_le_left _ _)),
    (hx.trans_le (min_le_right _ _)).le⟩

theorem isOpen_range_pow' (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hd : HasStrictDerivAt (fun x : K => x ^ n) ((n : K) * 1 ^ (n - 1)) 1 := hasStrictDerivAt_pow n 1
  have hne : ((n : K) * 1 ^ (n - 1)) ≠ 0 := by
    rw [one_pow, mul_one]; exact_mod_cast hn.ne'
  have hm := hd.map_nhds_eq hne
  simp only [one_pow] at hm
  have hr : Set.range (fun x : K => x ^ n) ∈ nhds (1 : K) := by
    rw [← hm]; exact Filter.range_mem_map
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap, Units.val_one]
  refine ⟨_, hr, ?_⟩
  rintro y ⟨x, hx⟩
  have hx' : x ^ n = (y : K) := hx
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hx'
    exact y.ne_zero hx'.symm
  exact ⟨Units.mk0 x h0, Units.ext (by simpa using hx')⟩

theorem finiteIndex_of_isOpen_of_vK (hK : FiniteDimensional ℚ_[p] K) (H : Subgroup Kˣ)
    (hH : IsOpen (H : Set Kˣ)) {x : Kˣ} (hx : x ∈ H) (hv : vK p K x ≠ 0) : H.FiniteIndex := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have : DiscreteTopology (Kˣ ⧸ H) := QuotientGroup.discreteTopology hH
  set m := vK p K x with hm
  let C : Set Kˣ := ⋃ j ∈ Finset.range m.natAbs, (fun u => π ^ j * u) '' (UK p K : Set Kˣ)
  have hC : IsCompact C :=
    (Finset.range m.natAbs).isCompact_biUnion fun j _ =>
      (isCompact_UK' hK).image (continuous_const.mul continuous_id)
  have hfin : ((QuotientGroup.mk : Kˣ → Kˣ ⧸ H) '' C).Finite :=
    (hC.image QuotientGroup.continuous_mk).finite_of_discrete
  have hall : (QuotientGroup.mk : Kˣ → Kˣ ⧸ H) '' C = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    have hj0 : 0 ≤ vK p K y % m := Int.emod_nonneg _ hv
    have hj1 : vK p K y % m < |m| := Int.emod_lt_abs _ hv
    set j := (vK p K y % m).toNat with hj
    have hjc : (j : ℤ) = vK p K y % m := Int.toNat_of_nonneg hj0
    set k := vK p K y / m with hk
    have hu : (π ^ j)⁻¹ * y * (x ^ k)⁻¹ ∈ UK p K := by
      rw [mem_UK_iff p K hK, vK_mul, vK_mul, vK_inv, vK_inv, vK_pow, vK_zpow, hπ, hjc, ← hm]
      have := Int.emod_add_mul_ediv (vK p K y) m
      rw [← hk] at this
      linarith [mul_comm m k]
    refine ⟨π ^ j * ((π ^ j)⁻¹ * y * (x ^ k)⁻¹), ?_, ?_⟩
    · refine Set.mem_biUnion (x := j) ?_ ⟨_, hu, rfl⟩
      rw [Finset.coe_range, Set.mem_Iio]
      have : (j : ℤ) < (m.natAbs : ℤ) := by rw [hjc, Int.natCast_natAbs]; exact hj1
      exact_mod_cast this
    · rw [QuotientGroup.eq]
      have : (π ^ j * ((π ^ j)⁻¹ * y * (x ^ k)⁻¹))⁻¹ * y = x ^ k := by group
      rw [this]
      exact H.zpow_mem hx k
  have : Finite (Kˣ ⧸ H) := by
    rw [← Set.finite_univ_iff, ← hall]; exact hfin
  exact Subgroup.finiteIndex_of_finite_quotient

theorem finiteIndex_range_pow' (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  refine finiteIndex_of_isOpen_of_vK hK _ (isOpen_range_pow' hK hn) (x := π ^ n) ⟨π, rfl⟩ ?_
  rw [vK_pow, hπ, mul_one]
  exact_mod_cast hn.ne'

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBA
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function ReciprocityTheory.Neutral.Cmp

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

theorem Model.E_algebraMap_integer (c : 𝒪[K]) :
    m.E (algebraMap 𝒪[K] (AlgebraicClosure K) c) = (m.e (c : K) : PadicAlgCl p) := m.comm _

theorem Model.mem_integral_closure_iff_norm (x : AlgebraicClosure K) : x ∈ integersBar K ↔ ‖m.E x‖ ≤ 1 := by
  constructor
  · rintro ⟨P, hPm, hP⟩
    let f : 𝒪[K] →+* PadicAlgCl p :=
      (m.E : AlgebraicClosure K →+* PadicAlgCl p).comp (algebraMap 𝒪[K] (AlgebraicClosure K))
    refine norm_le_one_of_monic_root (P.map f) (hPm.map f) (fun i => ?_) ?_
    · rw [Polynomial.coeff_map]
      show ‖m.E (algebraMap 𝒪[K] (AlgebraicClosure K) (P.coeff i))‖ ≤ 1
      rw [m.E_algebraMap_integer]
      exact (m.int _).1 (P.coeff i).2
    · have := congrArg (m.E : AlgebraicClosure K →+* PadicAlgCl p) hP
      rw [map_zero, Polynomial.hom_eval₂] at this
      rw [Polynomial.eval_map]
      exact this
  · intro hy
    obtain ⟨q, hqm, hq⟩ := (norm_le_one_iff_isIntegral (m.E x)).1 hy
    let ψ : PadicInt.subring p →+* 𝒪[K] :=
      ((m.e.symm : m.K' →+* K).comp ((algebraMap ℚ_[p] m.K').comp (PadicInt.subring p).subtype)).codRestrict
        𝒪[K] (fun c => (m.int _).2 (by
          show ‖((m.e (m.e.symm (algebraMap ℚ_[p] m.K' (c : ℚ_[p]))) : m.K') : PadicAlgCl p)‖ ≤ 1
          rw [RingEquiv.apply_symm_apply]
          show ‖algebraMap ℚ_[p] (PadicAlgCl p) (c : ℚ_[p])‖ ≤ 1
          rw [norm_algebraMap']
          exact c.2))
    refine ⟨q.map ψ, hqm.map ψ, ?_⟩
    apply m.E.injective
    rw [Polynomial.eval₂_map, map_zero]
    have := Polynomial.hom_eval₂ q ((algebraMap 𝒪[K] (AlgebraicClosure K)).comp ψ)
      (m.E : AlgebraicClosure K →+* PadicAlgCl p) x
    change (m.E : AlgebraicClosure K →+* PadicAlgCl p) _ = 0
    rw [this, ← hq]
    congr 1
    ext c
    show m.E (algebraMap 𝒪[K] (AlgebraicClosure K) (ψ c)) = _
    rw [m.E_algebraMap_integer]
    show ((m.e (m.e.symm (algebraMap ℚ_[p] m.K' (c : ℚ_[p]))) : m.K') : PadicAlgCl p) = _
    rw [RingEquiv.apply_symm_apply]
    rfl

theorem Model.mem_maximal_ideal_closure_iff_norm (x : AlgebraicClosure K) : x ∈ maxIdealBar K ↔ ‖m.E x‖ < 1 := by
  show (x ∈ integersBar K ∧ (x = 0 ∨ x⁻¹ ∉ integersBar K)) ↔ _
  rw [m.mem_integral_closure_iff_norm, m.mem_integral_closure_iff_norm]
  by_cases h0 : x = 0
  · simp [h0]
  · have hn : 0 < ‖m.E x‖ := norm_pos_iff.2 (by simpa using h0)
    rw [map_inv₀, norm_inv]
    simp only [h0, false_or, not_le]
    rw [one_lt_inv_iff₀]
    exact ⟨fun h => h.2.2, fun h => ⟨h.le, hn, h⟩⟩

noncomputable def Model.toOK : 𝒪[K] →+* OK p m.K' :=
  ((m.e : K →+* m.K').comp 𝒪[K].subtype).codRestrict _ (fun c => (mem_OK_iff p m.K' _).2 ((m.int _).1 c.2))

theorem Model.toOK_surjective : Surjective m.toOK := by
  intro y
  refine ⟨⟨m.e.symm y, (m.int _).2 ?_⟩, ?_⟩
  · rw [RingEquiv.apply_symm_apply]
    exact (mem_OK_iff p m.K' _).1 y.2
  · apply Subtype.ext
    show m.e (m.e.symm y) = y
    rw [RingEquiv.apply_symm_apply]

theorem Model.card_residue_field_model [IsNonarchimedeanLocalField K] : Nat.card 𝓀[K] = qK p m.K' := by
  let f : 𝒪[K] →+* resK p m.K' := (redK p m.K').comp m.toOK
  have hf : Surjective f := (redK_surjective p m.K').comp m.toOK_surjective
  have hker : RingHom.ker f = IsLocalRing.maximalIdeal 𝒪[K] :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hf)
  rw [qK]
  exact Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)).toEquiv

theorem Model.mem_integer_iff_vK (x : Kˣ) : (x : K) ∈ 𝒪[K] ↔ 0 ≤ vK p m.K' (m.eU x) := by
  rw [m.int, ← norm_le_one_iff_vK p m.K' m.fin]
  rfl

theorem Model.isUnit_integer_iff (x : Kˣ) (hx : (x : K) ∈ 𝒪[K]) :
    IsUnit (⟨x, hx⟩ : 𝒪[K]) ↔ vK p m.K' (m.eU x) = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]).1 = ((x⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val]
      apply eq_inv_of_mul_eq_one_left
      have h2 : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (u : 𝒪[K]) = 1 := u.inv_mul
      rw [hu] at h2
      exact congrArg Subtype.val h2
    have h3 : ((x⁻¹ : Kˣ) : K) ∈ 𝒪[K] := h1 ▸ ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]).2
    rw [m.mem_integer_iff_vK, map_inv, vK_inv] at h3
    rw [m.mem_integer_iff_vK] at hx
    omega
  · intro h
    have h3 : ((x⁻¹ : Kˣ) : K) ∈ 𝒪[K] := by
      rw [m.mem_integer_iff_vK, map_inv, vK_inv, h]; simp
    exact IsUnit.of_mul_eq_one ⟨_, h3⟩ (Subtype.ext (by simp))

theorem Model.isUniformiser_iff_valuation_one (π : Kˣ) : IsUniformiser K (π : K) ↔ vK p m.K' (m.eU π) = 1 := by
  constructor
  · rintro ⟨hπ, hirr⟩
    obtain ⟨ϖ', hϖ'⟩ := exists_vK_eq_one p m.K' m.fin
    obtain ⟨ϖ, rfl⟩ := m.eU.surjective ϖ'
    have h0 := (m.mem_integer_iff_vK π).1 hπ
    have h1 : vK p m.K' (m.eU π) ≠ 0 := fun h => hirr.not_isUnit ((m.isUnit_integer_iff π hπ).2 h)
    have hϖ : (ϖ : K) ∈ 𝒪[K] := by rw [m.mem_integer_iff_vK, hϖ']; exact zero_le_one
    have hv : vK p m.K' (m.eU (ϖ⁻¹ * π)) = vK p m.K' (m.eU π) - 1 := by
      rw [map_mul, vK_mul, map_inv, vK_inv, hϖ']; ring
    have hq : ((ϖ⁻¹ * π : Kˣ) : K) ∈ 𝒪[K] := by
      rw [m.mem_integer_iff_vK, hv]; omega
    have hmul : (⟨π, hπ⟩ : 𝒪[K]) = ⟨ϖ, hϖ⟩ * ⟨_, hq⟩ := Subtype.ext (by simp)
    rcases hirr.isUnit_or_isUnit hmul with h | h
    · rw [m.isUnit_integer_iff, hϖ'] at h; omega
    · rw [m.isUnit_integer_iff, hv] at h; omega
  · intro h
    have hπ : (π : K) ∈ 𝒪[K] := by rw [m.mem_integer_iff_vK, h]; exact zero_le_one
    refine ⟨hπ, ?_, ?_⟩
    · rw [m.isUnit_integer_iff, h]; omega
    · intro a b hab
      have hab' : (π : K) = a.1 * b.1 := congrArg Subtype.val hab
      have ha0 : a.1 ≠ 0 := fun h0 => π.ne_zero (by rw [hab', h0, zero_mul])
      have hb0 : b.1 ≠ 0 := fun h0 => π.ne_zero (by rw [hab', h0, mul_zero])
      have hπab : π = Units.mk0 a.1 ha0 * Units.mk0 b.1 hb0 := Units.ext hab'
      have ha := (m.mem_integer_iff_vK (Units.mk0 a.1 ha0)).1 a.2
      have hb := (m.mem_integer_iff_vK (Units.mk0 b.1 hb0)).1 b.2
      rw [hπab, map_mul, vK_mul] at h
      have h2 : vK p m.K' (m.eU (Units.mk0 a.1 ha0)) = 0 ∨ vK p m.K' (m.eU (Units.mk0 b.1 hb0)) = 0 := by omega
      exact h2.imp (fun h => (m.isUnit_integer_iff (Units.mk0 a.1 ha0) a.2).2 h)
        (fun h => (m.isUnit_integer_iff (Units.mk0 b.1 hb0) b.2).2 h)

theorem Model.isHomeomorph_units_model : IsHomeomorph m.eU := by
  have h1 : Continuous m.eU := Continuous.units_map (m.e : K →* m.K') m.homeo.continuous
  have h2 : Continuous m.eU.symm :=
    Continuous.units_map (m.e.symm : m.K' →* K) (m.e.toEquiv.toHomeomorphOfContinuousOpen m.homeo.continuous m.homeo.isOpenMap).symm.continuous
  exact (Homeomorph.mk m.eU.toEquiv h1 h2).isHomeomorph

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

