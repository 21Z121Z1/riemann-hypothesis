import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PhiSub
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem phi_sub (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hΦ : PhiCond Γ l) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) : PhiCond H l := by
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hΦ _ hK'
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  have hc : Continuous (e.symm : K.map H.subtype → K) := by
    have hind : Topology.IsInducing (fun k : K => ((k : H) : Γ)) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    rw [hind.continuous_iff]
    have hfun : (fun k : K => ((k : H) : Γ)) ∘ e.symm = fun γ : K.map H.subtype => (γ : Γ) := by
      funext γ
      have h1 := K.coe_equivMapOfInjective_apply H.subtype H.subtype_injective (e.symm γ)
      simp only [Function.comp_apply]
      rw [← H.coe_subtype, ← h1]
      simp [e]
    rw [hfun]
    exact continuous_subtype_val
  refine Finite.of_injective
    (β := {ψ : (K.map H.subtype) →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, ?_⟩) ?_
  · have hk : ((φ.1.comp e.symm.toMonoidHom).ker : Set (K.map H.subtype)) = e.symm ⁻¹' (φ.1.ker : Set K) := by
      ext γ
      exact Iff.rfl
    rw [hk]
    exact φ.2.preimage hc
  · intro φ φ' h
    apply Subtype.ext
    ext k
    have h2 := congrArg (fun ψ => ψ.1 (e k)) h
    simpa using h2

private theorem finite_addMonoidHom_zmod_of_finite (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Finite M] :
    Finite (M →+ ZMod l) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact Finite.of_injective (fun f : M →+ ZMod l => (f : M → ZMod l)) DFunLike.coe_injective

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (hl : ∀ m : M, l • m = 0)
    (m : M) (h : ∀ f : M →+ ZMod l, f m = 0) : m = 0 := by
  letI : Module (ZMod l) M := AddCommGroup.zmodModule hl
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  apply b.repr.injective
  ext i
  have := h (b.coord i).toAddMonoidHom
  rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  simpa using this

theorem UpperTheory.V.Pa.finZ :
    ∀ (l : ℕ) [Fact l.Prime] (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l • m = 0) → Finite (Zl ρ) ∧ ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → PhiCond H l := by
  intro l _ R Γ M _ _ _ _ _ _ _ _ ρ hΦ hρ hl
  refine ⟨?_, fun H hH => phi_sub l hΦ H hH⟩
  let N : Subgroup Γ :=
    { carrier := {g | ∀ m, ρ g m = m}
      mul_mem' := by
        intro a b ha hb m
        simp only [Set.mem_setOf_eq] at ha hb
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        intro m
        simp
      inv_mem' := by
        intro a ha m
        simp only [Set.mem_setOf_eq] at ha
        have h1 := ha (ρ a⁻¹ m)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
        exact h1.symm }
  have hN : IsOpen (N : Set Γ) := by
    have hset : (N : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp [N]
    rw [hset]
    exact isOpen_iInter_of_finite (fun m => (hρ m).isOpen_fiber m)
  haveI : Finite (Γ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  haveI : Finite (M →+ ZMod l) := finite_addMonoidHom_zmod_of_finite l M
  haveI := hΦ N hN
  have z1 : ∀ z ∈ Zl ρ, z 1 = 0 := by
    intro z hz
    have h := ((mem_Zl ρ).1 hz).2 1 1
    simpa using h
  have zN : ∀ z ∈ Zl ρ, ∀ a b : Γ, a ∈ N → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [((mem_Zl ρ).1 hz).2, ha]
  refine Finite.of_injective
    (β := (Γ ⧸ N → M) × ((M →+ ZMod l) →
      {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}))
    (fun z => (fun q => z.1 q.out, fun f =>
      ⟨⟨⟨fun k => Multiplicative.ofAdd (f (z.1 k)), ?_⟩, ?_⟩, ?_⟩)) ?_
  · show Multiplicative.ofAdd (f (z.1 ((1 : N) : Γ))) = 1
    rw [Subgroup.coe_one, z1 _ z.2, map_zero, ofAdd_zero]
  · intro k k'
    show Multiplicative.ofAdd (f (z.1 ((k * k' : N) : Γ))) =
      Multiplicative.ofAdd (f (z.1 k)) * Multiplicative.ofAdd (f (z.1 k'))
    rw [Subgroup.coe_mul, zN _ z.2 _ _ k.2, map_add, ofAdd_add]
  · have hlc : IsLocallyConstant (fun k : N => Multiplicative.ofAdd (f (z.1 k))) :=
      (((mem_Zl ρ).1 z.2).1.comp_continuous continuous_subtype_val).comp _
    rw [MonoidHom.coe_ker]
    exact hlc.isOpen_fiber 1
  · intro z z' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    funext g
    have key : ∀ k : N, z.1 k = z'.1 k := by
      intro k
      have hf : ∀ f : M →+ ZMod l, f (z.1 k - z'.1 k) = 0 := by
        intro f
        have h3 := congrArg (fun ψ : {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)} =>
          Multiplicative.toAdd (ψ.1 k)) (congrFun h2 f)
        simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h3
        rw [map_sub, h3, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul l M hl _ hf)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N g
    have hg : g = (QuotientGroup.mk g : Γ ⧸ N).out * ((k⁻¹ : N) : Γ) := by
      rw [hk]
      simp [mul_assoc]
    have h1' : z.1 (QuotientGroup.mk g : Γ ⧸ N).out = z'.1 (QuotientGroup.mk g : Γ ⧸ N).out :=
      congrFun h1 (QuotientGroup.mk g)
    rw [hg, ((mem_Zl ρ).1 z.2).2, ((mem_Zl ρ).1 z'.2).2, key, h1']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem polZ_mem {l : ℕ} [Fact l.Prime] (F : GFrame l) {γ : F.Γ} (h : γ ∉ F.η.ker) : γ * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at h ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η γ) with h1 | h1
  · exact absurd h1 h
  · rw [h1]
    decide

private theorem polZ_nmem {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : (g : F.Γ) * F.c ∉ F.η.ker := by
  rw [MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.mp g.2, F.η_c, one_mul]
  decide

private theorem polZ_proj {l : ℕ} [Fact l.Prime] (F : GFrame l) :
    ∃ p : F.Γ → F.G₀, Continuous p ∧ (∀ g : F.G₀, p g = g) ∧ ∀ g : F.G₀, p (g * F.c) = g := by
  have hK : IsClopen (F.η.ker : Set F.Γ) :=
    ⟨Subgroup.isClosed_of_isOpen _ F.η_open, F.η_open⟩
  have hfr : frontier {a : F.Γ | a ∈ F.η.ker} = ∅ := hK.frontier_eq
  have hf : Continuous fun γ : F.Γ => if γ ∈ F.η.ker then (1 : F.Γ) else F.c := by
    refine continuous_if ?_ continuousOn_const continuousOn_const
    intro a ha
    rw [hfr] at ha
    exact ha.elim
  refine ⟨fun γ => ⟨γ * (if γ ∈ F.η.ker then 1 else F.c), by
    split_ifs with hγ
    · simpa using hγ
    · exact polZ_mem F hγ⟩, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_id.mul hf) _
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * (if (g : F.Γ) ∈ F.η.ker then 1 else F.c) = g
    rw [if_pos g.2, mul_one]
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * F.c * (if (g : F.Γ) * F.c ∈ F.η.ker then 1 else F.c) = g
    rw [if_neg (polZ_nmem F g), mul_assoc, F.c_sq, mul_one]

private theorem polZ_cases {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, polZ_mem F h⟩, ?_⟩
    show γ = γ * F.c * F.c
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) :
    (F.conj g : F.Γ) = F.c * g * F.c := by
  show F.c * g * F.c⁻¹ = _
  rw [inv_eq_of_mul_eq_one_right F.c_sq]

private theorem polZ_ext {l : ℕ} [Fact l.Prime] (F : GFrame l) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (rep : Representation A F.Γ M) (Z : F.G₀ → M) (hl : IsLocallyConstant Z)
    (hm : ∀ g h, Z (g * h) = Z g + rep g (Z h)) (hc : ∀ g, Z (F.conj g) = rep F.c (Z g)) :
    ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = Z g := by
  classical
  obtain ⟨p, hp, hp1, hp2⟩ := polZ_proj F
  have hZ1 : Z 1 = 0 := by
    have h1 := hm 1 1
    simpa using h1
  have hpc : p F.c = 1 := by
    have h2 := hp2 1
    simpa using h2
  have hmem : (fun γ => Z (p γ)) ∈ Zl rep := by
    show IsLocallyConstant (fun γ => Z (p γ)) ∧
      ∀ g h : F.Γ, Z (p (g * h)) = Z (p g) + rep g (Z (p h))
    refine ⟨hl.comp_continuous hp, ?_⟩
    intro γ δ
    rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;>
      rcases polZ_cases F δ with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [← Subgroup.coe_mul]
      simp only [hp1]
      exact hm g h
    · rw [show (g : F.Γ) * (h * F.c) = ((g * h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, mul_assoc]]
      simp only [hp1, hp2]
      exact hm g h
    · rw [show (g : F.Γ) * F.c * h = ((g * F.conj h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc, F.c_sq, mul_one]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
    · rw [show (g : F.Γ) * F.c * (h * F.c) = ((g * F.conj h : F.G₀) : F.Γ) by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
  refine ⟨fun γ => Z (p γ), hmem, ?_, fun g => ?_⟩
  · show Z (p F.c) = 0
    rw [hpc, hZ1]
  · show Z (p g) = Z g
    rw [hp1]

theorem UpperTheory.V.Pa.polZ :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (rep : Representation A F.Γ V), IsAd F ρ χ V rep → (∀ z : F.G₀ → Matrix (Fin n) (Fin n) R, (∀ g, z g ∈ V) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹)) → (∀ g, z (F.conj g) = -(χ F.c • (z g)ᵀ)) → ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, (y g : Matrix (Fin n) (Fin n) R) = z g) ∧ (∀ y ∈ Zl rep, y F.c = 0 → (∀ g : F.G₀, (y (F.conj g) : Matrix (Fin n) (Fin n) R) = -(χ F.c • (y g : Matrix (Fin n) (Fin n) R)ᵀ)) ∧ ((∀ g : F.G₀, y g = 0) → y = 0)) := by
  intro l _ F A R _ _ _ n ρ χ V rep hAd
  obtain ⟨hA1, hA2⟩ := hAd
  refine ⟨fun z hz hzl hzm hzc => ?_, fun y hy hyc => ?_⟩
  · obtain ⟨y, hy, hyc, hyg⟩ := polZ_ext F rep (fun g => (⟨z g, hz g⟩ : V))
      (IsLocallyConstant.desc _ Subtype.val hzl Subtype.val_injective)
      (fun g h => Subtype.ext (by simp only [Submodule.coe_add, hA1]; exact hzm g h))
      (fun g => Subtype.ext (by rw [hA2]; exact hzc g))
    exact ⟨y, hy, hyc, fun g => by rw [hyg g]⟩
  · obtain ⟨-, hyc'⟩ := hy
    refine ⟨fun g => ?_, fun h0 => ?_⟩
    · rw [polZ_conj, hyc', hyc', hyc, map_zero, add_zero, zero_add, hA2]
    · funext γ
      rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · exact h0 g
      · rw [Pi.zero_apply, hyc', h0 g, hyc, map_zero, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SumCount
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumCount :
    ∀ (R D M : Type) [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R D M) (b : AddSubgroup M) (Z : AddSubgroup (D → M)), Finite Z → (∀ y ∈ b, (fun g => ρ g y - y) ∈ Z) → Finite ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) ∧ Nat.card ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) * Nat.card b ≤ Nat.card M * Nat.card Z := by
  intro R D M _ _ _ _ _ ρ b Z hZ hb
  let d : M →ₗ[R] (D → M) := LinearMap.pi fun g => ρ g - LinearMap.id
  have hd : ∀ y, d y = fun g => ρ g y - y := fun y => rfl
  let φ : M × Z →+ (D → M) := d.toAddMonoidHom.coprod Z.subtype
  have hφ : ∀ p : M × Z, φ p = d p.1 + p.2 := fun p => rfl
  have hr : φ.range = (Bl ρ).toAddSubgroup ⊔ Z := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hφ]
      exact AddSubgroup.add_mem_sup (show d p.1 ∈ (Bl ρ).toAddSubgroup from ⟨p.1, rfl⟩) p.2.2
    · refine sup_le ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨(y, 0), by rw [hφ]; exact add_zero _⟩
      · intro z hz
        exact ⟨(0, ⟨z, hz⟩), by rw [hφ]; simp⟩
  rw [← hr]
  have hfin : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  refine ⟨hfin, ?_⟩
  have h1 : Nat.card (M × Z) = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  have h2 : Nat.card b ≤ Nat.card φ.ker := by
    let ι : b → φ.ker := fun y => ⟨(y.1, -⟨fun g => ρ g y.1 - y.1, hb y.1 y.2⟩), by
      rw [AddMonoidHom.mem_ker, hφ, hd]
      exact add_neg_cancel _⟩
    refine Nat.card_le_card_of_injective ι fun y y' h => ?_
    exact Subtype.ext (congrArg (fun p : φ.ker => p.1.1) h)
  rw [← Nat.card_prod M Z, h1]
  exact Nat.mul_le_mul_left _ h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.TyCard
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem tc_perm {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : GL (Fin n) R) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w (σ i) i ≠ 0 := by
  by_contra h
  push Not at h
  have hd : (w : Matrix (Fin n) (Fin n) R).det = 0 := by
    rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    obtain ⟨i, hi⟩ := h σ
    have hp : ∏ j, (w : Matrix (Fin n) (Fin n) R) (σ j) j = 0 :=
      Finset.prod_eq_zero (f := fun j => (w : Matrix (Fin n) (Fin n) R) (σ j) j) (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  have hu : IsUnit (w : Matrix (Fin n) (Fin n) R).det := (Matrix.isUnit_iff_isUnit_det _).1 w.isUnit
  exact hu.ne_zero hd

private theorem tc_inv {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (b t : Fin n → Bool)
    (h : ∀ i j, b i ≠ t j → w i j = 0) (i j : Fin n) (e : t i ≠ b j) : (w⁻¹ : GL (Fin n) R) i j = 0 := by
  classical
  set M : Matrix (Fin n) (Fin n) R := (w : Matrix (Fin n) (Fin n) R) with hM
  set N : Matrix (Fin n) (Fin n) R := ((w⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hN
  let Dt : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if t k then 1 else 0
  let Db : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if b k then 1 else 0
  have hc : M * Dt = Db * M := by
    ext p q
    simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hpq : b p = t q
    · rw [hpq]; ring
    · rw [show M p q = 0 from h p q hpq]; simp
  have hNM : N * M = 1 := Units.inv_mul w
  have hMN : M * N = 1 := Units.mul_inv w
  have key : Dt * N = N * Db := by
    calc Dt * N = N * M * Dt * N := by rw [hNM, Matrix.one_mul]
      _ = N * (M * Dt) * N := by simp only [Matrix.mul_assoc]
      _ = N * (Db * M) * N := by rw [hc]
      _ = N * Db * (M * N) := by simp only [Matrix.mul_assoc]
      _ = N * Db := by rw [hMN, Matrix.mul_one]
  have hij := congrFun (congrFun key i) j
  simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  cases hti : t i <;> cases hbj : b j <;> simp [hti, hbj] at hij e ⊢ <;>
    first | exact hij | exact hij.symm

private theorem tc_same {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card =
      (Finset.univ.filter fun i => t i = true).card.choose 2 +
        (Finset.univ.filter fun i => ¬ t i = true).card.choose 2 := by
  classical
  have hU : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2) =
      ((Finset.univ.filter fun i => t i = true) ×ˢ (Finset.univ.filter fun i => t i = true)).filter
          (fun p => p.1 < p.2) ∪
        ((Finset.univ.filter fun i => ¬ t i = true) ×ˢ
          (Finset.univ.filter fun i => ¬ t i = true)).filter (fun p => p.1 < p.2) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product]
    cases t x <;> cases t y <;> simp
  rw [hU, Finset.card_union_of_disjoint, Finset.card_product_filter_lt,
    Finset.card_product_filter_lt]
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2
  exact h2.1.1 h1.1.1

private theorem tc_diff {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card =
      (Finset.univ.filter fun i => t i = true).card *
        (Finset.univ.filter fun i => ¬ t i = true).card := by
  classical
  have hsplit : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact h2.2.2 h1.2.2
  have htot : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n.choose 2 := by
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have hcard : (Finset.univ.filter fun i => t i = true).card +
      (Finset.univ.filter fun i => ¬ t i = true).card = n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hch : ∀ a b : ℕ, (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
    intro a b
    induction b with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ', Nat.choose_succ_succ' k, Nat.choose_one_right,
        Nat.choose_one_right, ih]
      ring
  have hh := hch (Finset.univ.filter fun i => t i = true).card
    (Finset.univ.filter fun i => ¬ t i = true).card
  rw [hcard] at hh
  rw [htot, tc_same t] at hsplit
  linarith

theorem UpperTheory.V.Pa.tyCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (v : F.Vl) (g : ℕ), (Finset.univ.filter fun i => x.ty v i = true).card = x.a ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 = x.ty v p.2).card + g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = nu n x.a g ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = x.a * (n - x.a) ∧ ∀ i j : Fin n, x.ty v i ≠ decide ((j : ℕ) < x.a) → ((x.w v)⁻¹ : GL (Fin n) x.A) i j = 0 := by
  intro l _ F n x v g
  classical
  obtain ⟨σ, hσ⟩ := tc_perm (x.w v)
  have hty : ∀ j, x.ty v j = decide (((σ j : Fin n) : ℕ) < x.a) := by
    intro j
    by_contra hne
    exact hσ j (x.w_blk v (σ j) j (Ne.symm hne))
  have hT : (Finset.univ.filter fun i => x.ty v i = true).card = x.a := by
    rw [← Fintype.card_subtype, ← Fintype.card_fin_lt_of_le x.a_le]
    refine Fintype.card_congr (Equiv.subtypeEquiv σ fun j => ?_)
    rw [hty j]
    simp
  have hF : (Finset.univ.filter fun i => ¬ x.ty v i = true).card = n - x.a := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => x.ty v i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [tc_same, tc_diff, hT, hF]
    simp [nu]
  · rw [tc_diff, hT, hF]
  · intro i j e
    exact tc_inv (x.w v) (fun k => decide ((k : ℕ) < x.a)) (x.ty v)
      (fun p q hpq => x.w_blk v p q hpq) i j e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ul_cop (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (n : ℕ) :
    (Nat.card (Fin n → kˣ)).Coprime l := by
  classical
  haveI := Fintype.ofFinite k
  have hl : l.Prime := Fact.out
  obtain ⟨m, -, hm⟩ := FiniteField.card k l
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_units, hm]
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
  intro hd
  have h1 : l ∣ l ^ (m : ℕ) := dvd_pow_self l m.ne_zero
  have h2 : 1 ≤ l ^ (m : ℕ) := Nat.one_le_pow _ _ hl.pos
  have h3 := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self h2] at h3
  exact hl.one_lt.ne' (Nat.dvd_one.mp h3)

private theorem ul_ker {G C : Type} [Group G] [Group C] {n : ℕ} (f : Fin n → G →* C) :
    (MonoidHom.pi f).ker = ⨅ i, (f i).ker := by
  ext g
  simp [MonoidHom.mem_ker, Subgroup.mem_iInf, funext_iff]

theorem UpperTheory.V.Pa.unrLoc :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∀ u, UnrCount l ((locOf r).Gu u) ((locOf r).Ju u) := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r u
  haveI : CharP (IsLocalRing.ResidueField O) l := IsCoef.char
  haveI : Finite (IsLocalRing.ResidueField O) := IsCoef.finite
  unfold locOf
  dsimp only
  have key : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v →
      UnrCount l (Dec (F := L) A) ((Ine A).subgroupOf (Dec (F := L) A) ⊓
        ⨅ i, ((r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype)).ker) := by
    intro A v hv
    let χ := MonoidHom.pi (fun i => (r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype))
    have hker : χ.ker = ⨅ i, ((r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype)).ker := ul_ker _
    have hopen : IsOpen (χ.ker : Set (Dec (F := L) A)) := by
      rw [hker, Subgroup.coe_iInf]
      refine isOpen_iInter_of_finite fun i => ?_
      exact (r.chib_open i).preimage ((V0.pr_cont continuous_resP).comp continuous_subtype_val)
    have h := unrBare l L Ω A v _ χ hv hopen (ul_cop l _ n)
    rwa [hker] at h
  exact key _ _ (s.hw _)
end

