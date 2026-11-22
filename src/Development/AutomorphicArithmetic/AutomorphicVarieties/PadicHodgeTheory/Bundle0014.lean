import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Bundle0003
import GroundTheory.LocalFields.KroneckerWeber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import GroundTheory.LocalFields.Bundle0014
import GroundTheory.LocalFields.PrincipalUnitsRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCochainsFinGenOfFinLevel
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
open ReciprocityTheory.Coh
variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

private noncomputable def redT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    TRep ℤ_[l] G :=
  { V := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) (m + 1)
    ccs := ⟨fun _ => continuous_of_discreteTopology⟩
    rho := redRep ρ (m + 1)
    cont := contAction_redRep h (m + 1) }

private instance redT_disc (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    DiscreteTopology (redT ρ h m).V := discrete_quot_lSub l n (m + 1)

private instance redT_fin (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Finite (redT ρ h m).V := finite_quot_lSub l n (m + 1)

private theorem lSub_le {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    lSub l X (m + 1) ≤ (lSub l X m).comap LinearMap.id := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_lSub.mp hx
  show (l : ℤ_[l]) ^ (m + 1) • y ∈ lSub l X m
  exact mem_lSub.mpr ⟨(l : ℤ_[l]) • y, by rw [pow_succ, mul_smul]⟩

private noncomputable def tauL (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    (X ⧸ lSub l X (m + 1)) →ₗ[ℤ_[l]] (X ⧸ lSub l X m) :=
  Submodule.mapQ _ _ LinearMap.id (lSub_le m)

private theorem tauL_mk {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) (x : X) :
    tauL l X m (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem tauL_equiv {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (ρ : Representation ℤ_[l] G X) (m : ℕ)
    (g : G) (y : X ⧸ lSub l X (m + 1)) : tauL l X m (redRep ρ (m + 1) g y) = redRep ρ m g (tauL l X m y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [redRep_mk, tauL_mk, tauL_mk, redRep_mk]

private theorem tauL_surj {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    Function.Surjective (tauL l X m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private noncomputable def tauT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair (redT ρ h (m + 1)) (redT ρ h m) :=
  Pair.ofMap (M := redT ρ h (m + 1)) (M' := redT ρ h m)
    (tauL l (Fin n → ℤ_[l]) (m + 1)) continuous_of_discreteTopology (tauL_equiv ρ (m + 1))

private noncomputable def piT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G) (redT ρ h m) :=
  Pair.ofMap (M := ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) (M' := redT ρ h m)
    (lSub l (Fin n → ℤ_[l]) (m + 1)).mkQ (continuous_mkQ _) (fun g x => (redRep_mk ρ (m + 1) g x).symm)

private theorem eq_zero_of_lSub (x : Fin n → ℤ_[l]) (hx : ∀ m, x ∈ lSub l (Fin n → ℤ_[l]) (m + 1)) : x = 0 := by
  funext i
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  rw [Pi.zero_apply, map_zero]
  cases k with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
    exact Subsingleton.elim _ _
  | succ k => exact mem_lSub_pi.mp (hx k) i

private theorem towerLim (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Cx.IsTowerLim (fun m => (redT ρ h m).coch) (fun m => (tauT ρ h m).hom)
      (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) fun m => (piT ρ h m).hom := by
  refine limRep_holds ℤ_[l] G (fun m => redT ρ h m) (tauT ρ h) _ (piT ρ h)
    (fun m => ⟨rfl, rfl, tauL_surj (m + 1), fun x => rfl⟩) ?_ ?_
  · have hc : Continuous fun (x : Fin n → ℤ_[l]) (m : ℕ) => (piT ρ h m).u x :=
      continuous_pi fun m => (piT ρ h m).u_cont
    refine (hc.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    rw [← sub_eq_zero]
    apply eq_zero_of_lSub
    intro m
    have := congr_fun hxy m
    exact (Submodule.Quotient.eq _).mp this
  · intro y hy
    let S : ℕ → Set (Fin n → ℤ_[l]) := fun m => (piT ρ h m).u ⁻¹' {y m}
    have hS : (⋂ m, S m).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      · intro m x hx
        show (piT ρ h m).u x = y m
        have hx' : (piT ρ h (m + 1)).u x = y (m + 1) := hx
        rw [← hy m, ← hx']
        rfl
      · intro m
        obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (y m)
        exact ⟨x, hx⟩
      · exact isCompact_univ.of_isClosed_subset
          ((isClosed_singleton).preimage (piT ρ h 0).u_cont) (Set.subset_univ _)
      · intro m
        exact (isClosed_singleton).preimage (piT ρ h m).u_cont
    obtain ⟨x, hx⟩ := hS
    exact ⟨x, fun m => Set.mem_iInter.mp hx m⟩

private theorem smul_emb (m : ℕ) : IsEmbedding fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ m • x := by
  have hc : (l : ℤ_[l]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine (Continuous.isClosedEmbedding (continuous_const_smul _) ?_).isEmbedding
  intro x y hxy
  funext i
  have := congr_fun hxy i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

private theorem finH {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) (M : TRep ℤ_[l] G) [Finite M.V]
    [DiscreteTopology M.V] : (∀ k, Finite (M.H k)) ∧ ∀ k, 2 < k → Subsingleton (M.H k) := by
  obtain ⟨h1, h2, h3, -, -⟩ := hF M.V M.rho M.cont
  obtain ⟨hN, ⟨e0, -⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := low_holds ℤ_[l] G M
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · match k with
    | 0 => exact Finite.of_equiv _ e0.symm.toEquiv
    | 1 => exact Finite.of_equiv _ e1.symm.toEquiv
    | 2 => exact Finite.of_equiv _ e2.symm.toEquiv
    | k + 3 =>
      obtain ⟨e, -⟩ := hN (k + 3)
      haveI := h3 (k + 3) (by omega)
      exact Finite.of_equiv _ e.symm.toEquiv
  · obtain ⟨e, -⟩ := hN k
    haveI := h3 k (by omega)
    exact e.toEquiv.subsingleton

end

theorem UpperTheory.latticeCochains_finGen_of_finLevel :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ}, FinLevel l G χ d → ∀ {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 := by
  intro l _ G _ _ _ χ d hF n ρ h
  haveI : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ inferInstance
  have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hT := towerLim ρ h
  have htors : ∀ (k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      (l : ℤ_[l]) • x = 0 → x = 0 := by
    intro k x hx
    apply Subtype.ext
    funext g
    have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k =>
      z.1 g) hx
    exact (smul_eq_zero.mp this).resolve_left hl
  have hker : ∀ (m k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      ((piT ρ h m).hom.f k) x = 0 ↔ ∃ y, x = (l : ℤ_[l]) ^ (m + 1) • y := by
    intro m k x
    have key : ((piT ρ h m).hom.f k) x = 0 ↔
        ∀ g, x.1 g ∈ lSub l (Fin n → ℤ_[l]) (m + 1) := by
      constructor
      · intro hx g
        have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch (redT ρ h m)).X k =>
          z.1 g) hx
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      · intro hx
        apply Subtype.ext
        funext g
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hx g)
    rw [key]
    constructor
    · intro hx
      choose y hy using fun g => mem_lSub.mp (hx g)
      have hyc : Continuous y := by
        apply (smul_emb (n := n) (l := l) (m + 1)).continuous_iff.mpr
        have : (fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ (m + 1) • x) ∘ y =
            x.1 := funext hy
        rw [this]
        exact x.2
      refine ⟨⟨y, hyc⟩, ?_⟩
      apply Subtype.ext
      funext g
      exact (hy g).symm
    · rintro ⟨y, rfl⟩ g
      exact mem_lSub.mpr ⟨y.1 g, rfl⟩
  have hfin : ∀ m, (∀ k, Finite ((redT ρ h m).H k)) ∧ ∀ k, 2 < k → Subsingleton ((redT ρ h m).H k) :=
    fun m => finH hF (redT ρ h m)
  have hlen0 : ∀ k, IsFiniteLength ℤ_[l] ((redT ρ h 0).coch.H k) := fun k => by
    haveI := (hfin 0).1 k
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have res := ReciprocityTheory.Coh.finGen_holds ℤ_[l] (l : ℤ_[l]) _ _ _ _ hT htors hker hlen0
  refine ⟨fun k => (res k).1, fun k hk => ?_⟩
  have ext := (ReciprocityTheory.Coh.tower_holds ℤ_[l] _ _ _ _ hT k).2 (fun j _ m => by
    haveI := (hfin m).1 j
    infer_instance)
  refine ⟨fun a b => ?_⟩
  have ha := ext a (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  have hb := ext b (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  rw [ha, hb]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MuNone
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc Topology

private theorem mn_sep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (h : TopologicalAbelianization G) (hh : h ≠ 1) :
    ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ h ∉ V := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  have hg : g ∉ (commutator G).topologicalClosure := fun hm => hh ((QuotientGroup.eq_one_iff g).2 hm)
  have hS : IsOpen {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} :=
    (Subgroup.isClosed_topologicalClosure _).isOpen_compl.preimage (continuous_mul_right g)
  have h1 : (1 : G) ∈ {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} := by
    show 1 * g ∉ ((commutator G).topologicalClosure : Set G)
    rw [one_mul]
    exact hg
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1
  refine ⟨(W : Subgroup G).map (QuotientGroup.mk' _), ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ W.isOpen
  · rintro ⟨w, hw, he⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    exact hW (inv_mem hw) he

private theorem mn_core {A M : Type} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [CommGroup M] (r : M →* A) (hr : DenseRange r) {q : ℕ} (hq : q ≠ 0)
    (hM : ∀ x : M, x ^ q = 1 → x = 1)
    (hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set A, IsOpen V ∧ 1 ∈ V ∧ ∀ x, r x ∈ V → ∃ z, x = z ^ n)
    (a : A) (ha : a ^ q = 1) (n : ℕ) (hn : n ≠ 0) : ∃ z, a = z ^ n := by
  have hP : IsClosed (Set.range fun z : A => z ^ n) := (isCompact_range (continuous_pow n)).isClosed
  obtain ⟨V, hVo, hV1, hV⟩ := hopen (q * n) (mul_ne_zero hq hn)
  suffices hs : a ∈ closure (Set.range fun z : A => z ^ n) by
    rw [hP.closure_eq] at hs
    obtain ⟨z, hz⟩ := hs
    exact ⟨z, hz.symm⟩
  rw [mem_closure_iff]
  intro o ho hao
  have hW : IsOpen (o ∩ {y : A | y ^ q ∈ V}) := ho.inter (hVo.preimage (continuous_pow q))
  have haW : a ∈ o ∩ {y : A | y ^ q ∈ V} := ⟨hao, by show a ^ q ∈ V; rw [ha]; exact hV1⟩
  obtain ⟨x, hx1, hx2⟩ := hr.exists_mem_open hW ⟨a, haW⟩
  have hx3 : r (x ^ q) ∈ V := by
    rw [map_pow]
    exact hx2
  obtain ⟨z, hz⟩ := hV (x ^ q) hx3
  have hxz : x = z ^ n := by
    have h1 : (x * (z ^ n)⁻¹) ^ q = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, mul_comm n q, ← hz, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hM _ h1)
  exact ⟨r x, hx1, r z, by rw [hxz, map_pow]⟩

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
private theorem mn_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {q : ℕ} (hq : q ≠ 0) (hM : ∀ x : Kˣ, x ^ q = 1 → x = 1)
    (a : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) (ha : a ^ q = 1) : a = 1 := by
  haveI : IsClosed ((commutator (Ω ≃ₐ[K] Ω)).topologicalClosure : Set (Ω ≃ₐ[K] Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set (TopologicalAbelianization (Ω ≃ₐ[K] Ω)), IsOpen V ∧ 1 ∈ V ∧
      ∀ x, localReciprocityLimit K Ω x ∈ V → ∃ z, x = z ^ n := by
    intro n hn
    haveI : Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := finite_quotient_range_pow_of_charZero hn
    let H : openFiniteIndex Kˣ := ⟨(powMonoidHom n : Kˣ →* Kˣ).range,
      isOpen_range_pow (Nat.cast_ne_zero.mpr hn), Subgroup.finiteIndex_of_finite_quotient⟩
    haveI := openCompletion.discreteTopology_quotient H
    refine ⟨(fun b => artinCoord K Ω H (topologicalAbelianizationEquiv K Ω b)) ⁻¹' {1}, ?_, ?_, ?_⟩
    · exact (isOpen_discrete _).preimage
        ((continuous_artinCoord H).comp (topologicalAbelianizationEquiv K Ω).continuous)
    · show artinCoord K Ω H (topologicalAbelianizationEquiv K Ω 1) = 1
      rw [map_one, map_one]
    · intro x hx
      have hx' : artinCoord K Ω H (topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x)) = 1 := hx
      rw [← localArtinMap_apply, artinCoord_localArtinMap, QuotientGroup.eq_one_iff] at hx'
      obtain ⟨z, hz⟩ := hx'
      exact ⟨z, hz.symm⟩
  have hall : ∀ n : ℕ, n ≠ 0 → ∃ z, a = z ^ n := fun n hn =>
    mn_core (localReciprocityLimit K Ω) denseRange_localReciprocityLimit hq hM hopen a ha n hn
  by_contra hne
  obtain ⟨V, hVo, haV⟩ := mn_sep a hne
  haveI : Finite (TopologicalAbelianization (Ω ≃ₐ[K] Ω) ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
  haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨z, hz⟩ := hall V.index Subgroup.FiniteIndex.index_ne_zero
  exact haV (hz ▸ Subgroup.pow_index_mem V z)

private theorem mn_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) {g : G}
    (hg : g ∈ (commutator G).topologicalClosure) : f g ∈ (commutator H).topologicalClosure := by
  have hc : commutator G ≤ (commutator H).comap f := by
    rw [← Subgroup.map_le_iff_le_comap, commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hcl : (commutator G).topologicalClosure ≤ ((commutator H).topologicalClosure).comap f :=
    Subgroup.topologicalClosure_minimal _ (hc.trans (Subgroup.comap_mono (Subgroup.le_topologicalClosure _)))
      ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  exact hcl hg

private theorem mn_cyc {l : ℕ} [Fact l.Prime] (σ : GQ l) {ζ : Om l} (h1 : ζ ^ l = 1) (h2 : ζ ≠ 1)
    (h : σ ζ = ζ) : PadicInt.toZMod ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have hp : l.Prime := Fact.out
  have hprim : IsPrimitiveRoot ζ l := by
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · exact h
  have hs := cyclotomicCharacter.spec (L := Om l) l (n := 1)
    (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ (by rw [pow_one]; exact h1)
  have hcyc : (cyc l l σ : ℤ_[l]ˣ) =
      cyclotomicCharacter (Om l) l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) := rfl
  rw [← hcyc] at hs
  set x : ℤ_[l] := ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) with hx
  have hσ : (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ = ζ := h
  have hs' : ζ ^ (PadicInt.toZModPow 1 x).val = ζ ^ 1 := by
    calc _ = _ := hs.symm
      _ = ζ := hσ
      _ = ζ ^ 1 := (pow_one ζ).symm
  have hlt : (PadicInt.toZModPow 1 x).val < l :=
    lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow (p := l) 1 x)) (pow_one l)
  have hk : (PadicInt.toZModPow 1 x).val = 1 := hprim.pow_inj hlt hp.one_lt hs'
  have hk' : PadicInt.toZModPow 1 x = 1 := by
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow 1 x), hk, Nat.cast_one]
  have hmem : x - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, map_sub, hk', map_one, sub_self]
  rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  exact hmem

theorem UpperTheory.V.Loc.muNone :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), (∃ g : G, PadicInt.toZMod ((cyc l l (φ g) : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∀ g : G, (QuotientGroup.mk' _ g : TopologicalAbelianization G) ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l → g ∈ (commutator G).topologicalClosure := by
  intro l _ G _ _ _ φ hφ hex g hg
  obtain ⟨g0, hg0⟩ := hex
  have hp : l.Prime := Fact.out
  obtain ⟨K, e, he1, he2, hφe, -⟩ := openField φ hφ
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  set L : IntermediateField ℚ_[l] (Om l) := K.1 with hL
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  haveI : IsAlgClosure L (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure L (Om l) := inferInstance
  obtain ⟨vr, ts, hloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] L
  let ψ : G →* Gal(Om l/L) := L.fixingSubgroupEquiv.toMonoidHom.comp e.toMonoidHom
  have hψ : Continuous ψ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).1.comp he1
  let ψi : Gal(Om l/L) →* G := e.symm.toMonoidHom.comp L.fixingSubgroupEquiv.symm.toMonoidHom
  have hψi : Continuous ψi := he2.comp (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).2
  have hψψ : ψi (ψ g) = g :=
    (congrArg e.symm (L.fixingSubgroupEquiv.symm_apply_apply (e g))).trans (e.symm_apply_apply g)
  obtain ⟨n, hn⟩ := hg
  have hgn : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply] at hn
    exact (QuotientGroup.eq_one_iff _).1 hn
  have hM : ∀ x : Lˣ, x ^ (l ^ n) = 1 → x = 1 := by
    intro x hx
    by_contra hx1
    obtain ⟨m, hmn, hm⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hx)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by rw [hm, pow_zero]))
    set y := x ^ (l ^ (m - 1)) with hy
    have hy1 : y ^ l = 1 := by
      rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← hm, pow_orderOf_eq_one]
    have hy2 : y ≠ 1 := by
      intro h
      have h3 := orderOf_dvd_of_pow_eq_one h
      rw [hm, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h3
      omega
    have hz1 : (((y : L) : Om l)) ^ l = 1 := by
      have h4 := congrArg (fun u : Lˣ => ((u : L) : Om l)) hy1
      simpa using h4
    have hz2 : (((y : L) : Om l)) ≠ 1 := by
      intro h
      apply hy2
      apply Units.ext
      apply Subtype.ext
      simpa using h
    have hσ : φ g0 ∈ GK K := by
      rw [← hφe]
      exact (e g0).2
    have hfix : (φ g0) ((y : L) : Om l) = ((y : L) : Om l) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (y : L).2
    exact hg0 (mn_cyc (φ g0) hz1 hz2 hfix)
  have hψn : ψ g ^ (l ^ n) ∈ (commutator Gal(Om l/L)).topologicalClosure := by
    rw [← map_pow]
    exact mn_map ψ hψ hgn
  have ha : QuotientGroup.mk' (commutator Gal(Om l/L)).topologicalClosure (ψ g) = 1 := by
    refine mn_field L (Om l) (pow_ne_zero n hp.ne_zero) hM _ ?_
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hψn
  rw [← hψψ]
  exact mn_map ψi hψi ((QuotientGroup.eq_one_iff _).1 ha)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NonemptyCohomologyRestrictScalarsLinearEquiv
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private def subEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' : Submodule Q X) (Z : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) : Z' ≃ₗ[Q] Z where
  toFun x := ⟨x.1, (hZ _).1 x.2⟩
  invFun x := ⟨x.1, (hZ _).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem quotEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' B' : Submodule Q X) (Z B : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) (hB : ∀ x, x ∈ B' ↔ x ∈ B) :
    Nonempty ((Z' ⧸ B'.comap Z'.subtype) ≃ₗ[Q] (Z ⧸ B.comap Z.subtype)) := by
  refine ⟨(Submodule.Quotient.equiv (B'.comap Z'.subtype) ((B.comap Z.subtype).restrictScalars Q)
    (subEq Z' Z hZ) ?_).trans (Submodule.Quotient.restrictScalarsEquiv Q (B.comap Z.subtype))⟩
  ext ⟨x, hx⟩
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : (y : X) = x := congrArg Subtype.val hyx
    show x ∈ B
    rw [← this]
    exact (hB _).1 hy
  · intro h
    exact ⟨⟨x, (hZ x).2 hx⟩, (hB x).2 h, rfl⟩

theorem UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv :
    ∀ (Q : Type) {A : Type} [CommRing Q] [CommRing A] [Algebra Q A] {G : Type} [Group G] [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [ContinuousConstSMul Q V] (ρ : Representation A G V), Nonempty (↥(H0 (resCoef Q ρ)) ≃ₗ[Q] ↥(H0 ρ)) ∧ Nonempty (H1 (resCoef Q ρ) ≃ₗ[Q] H1 ρ) ∧ Nonempty (H2 (resCoef Q ρ) ≃ₗ[Q] H2 ρ) ∧ ∀ n, Nonempty (Hn (resCoef Q ρ) n ≃ₗ[Q] Hn ρ n) := by
  intro Q A _ _ _ G _ _ V _ _ _ _ _ _ _ _ ρ
  have hd : ∀ n (f : (Fin n → G) → V), dn (resCoef Q ρ) n f = dn ρ n f := by
    intro n f
    funext g
    rw [dn_apply, dn_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul A ((-1 : Q) ^ ((j : ℕ) + 1))]
    simp
  refine ⟨⟨subEq _ _ fun x => Iff.rfl⟩, quotEq _ _ _ _ (fun x => Iff.rfl) ?_,
    quotEq _ _ _ _ (fun x => Iff.rfl) ?_, fun n => quotEq _ _ _ _ ?_ ?_⟩
  · intro x
    simp only [ReciprocityTheory.Gal.B1, LinearMap.mem_range]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.B2, Submodule.mem_map, mem_contMaps]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.Zn, Submodule.mem_inf, LinearMap.mem_ker, ReciprocityTheory.Gal.Cn,
      mem_contMaps, hd]
  · intro x
    cases n with
    | zero => simp [ReciprocityTheory.Gal.Bn]
    | succ n => simp only [ReciprocityTheory.Gal.Bn, Submodule.mem_map, ReciprocityTheory.Gal.Cn, mem_contMaps, hd]
end

