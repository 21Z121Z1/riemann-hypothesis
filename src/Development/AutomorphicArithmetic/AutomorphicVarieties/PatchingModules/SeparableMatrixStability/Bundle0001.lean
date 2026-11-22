import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0008
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CloseMap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.close_map :
    ∀ (Ph B Z : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (p : ∀ N, Γ N →* Z) (po : B →* Z) (U : Ultrafilter ℕ) (a : ∀ N, Γ N) (b : B) (z : Z), Continuous (po.comp πo) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), ∀ g, p N (π N g) * (po (πo g))⁻¹ ∈ W) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), p N (a N) * z⁻¹ ∈ W) → po b = z := by
  intro Ph B Z _ _ _ _ _ _ _ _ _ _ _ Γ _ π πo p po U a b z hf hp hclose ha
  set f : Ph →* Z := po.comp πo with hfdef
  have key : ∀ W : OpenNormalSubgroup Z, po b * z⁻¹ ∈ W := by
    intro W
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap f, W.isOpen.preimage hf⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' f }
    obtain ⟨N, h1, h2, h3⟩ := ((hp W).and ((hclose V).and (ha W))).exists
    obtain ⟨g, g', hg, hg', hV⟩ := h2
    have hV' : f (g⁻¹ * g') ∈ W := hV
    have e1 := h1 g
    rw [hg] at e1
    have hb : po b = f g' := by simp [hfdef, hg']
    have hn : f g' * (f g)⁻¹ ∈ W := by
      have hc := W.isNormal'.conj_mem _ hV' (f g)
      have he : f g * f (g⁻¹ * g') * (f g)⁻¹ = f g' * (f g)⁻¹ := by
        simp [map_mul, map_inv, mul_assoc]
      rw [he] at hc
      exact hc
    have hx : po b * z⁻¹ = (f g' * (f g)⁻¹) * (p N (a N) * (f g)⁻¹)⁻¹ * (p N (a N) * z⁻¹) := by
      rw [hb]; group
    rw [hx]
    exact W.mul_mem (W.mul_mem hn (W.inv_mem e1)) h3
  by_contra hne
  have hx1 : po b * z⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := po b * z⁻¹)) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CommLim
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem eventually_le_of_le_atTop {U : Filter ℕ} (h : U ≤ atTop) (n : ℕ) : ∀ᶠ N in U, n ≤ N :=
  h (eventually_ge_atTop n)

theorem UpperTheory.V.Pa.comm_lim :
    ∀ (l : ℕ) [Fact l.Prime] (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B] [TotallyDisconnectedSpace B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, IsTopologicalGroup (Γ N)] [∀ N, CompactSpace (Γ N)] [∀ N, TotallyDisconnectedSpace (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (ph ta : ∀ N, Γ N) (q : ℕ → ℕ) (a b : B), (U : Filter ℕ) ≤ atTop → (∀ N, Continuous (π N) ∧ Function.Surjective (π N)) → Continuous πo → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), (π N).ker ⊔ V.toSubgroup = πo.ker ⊔ V.toSubgroup) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ph N) a) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ta N) b) → (∀ N, q N ≡ 1 [MOD l ^ N]) → (∀ N, (ph N)⁻¹ * ta N * ph N = ta N ^ q N) → (∀ N (W : OpenNormalSubgroup (Γ N)), ∃ e : ℕ, ta N ^ l ^ e ∈ W) → a * b = b * a := by
  intro l _ Ph B _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ π πo U ph ta q a b hUa hπ hπo hker hph hta hq hrel hlw
  have hl : l.Prime := Fact.out
  have key : ∀ W : OpenNormalSubgroup B, (a * b)⁻¹ * (b * a) ∈ W.toSubgroup := by
    intro W
    haveI : W.toSubgroup.Normal := W.isNormal'
    haveI : Finite (B ⧸ W.toSubgroup) :=
      W.toSubgroup.quotient_finite_of_isOpen W.toOpenSubgroup.isOpen
    haveI : W.toSubgroup.FiniteIndex := W.toSubgroup.finiteIndex_of_finite_quotient
    have hn0 : W.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap πo, W.toOpenSubgroup.isOpen.preimage hπo⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' πo }
    have hVmem : ∀ x, x ∈ V.toSubgroup ↔ πo x ∈ W.toSubgroup := fun x => Iff.rfl
    obtain ⟨N, hNn, hk, h1, h2⟩ := ((eventually_le_of_le_atTop hUa W.toSubgroup.index).and
      ((hker V).and ((hph V).and (hta V)))).exists
    obtain ⟨g1, g1', e1, e1', hg1⟩ := h1
    obtain ⟨g2, g2', e2, e2', hg2⟩ := h2
    have hkV : (π N).ker ≤ V.toSubgroup := by
      have : (π N).ker ≤ πo.ker ⊔ V.toSubgroup := hk ▸ le_sup_left
      refine this.trans (sup_le ?_ le_rfl)
      intro x hx
      rw [hVmem, MonoidHom.mem_ker.mp hx]
      exact W.toSubgroup.one_mem
    set mk : B →* B ⧸ W.toSubgroup := QuotientGroup.mk' W.toSubgroup with hmk
    have eqmk : ∀ x y : Ph, x⁻¹ * y ∈ V.toSubgroup → mk (πo x) = mk (πo y) := by
      intro x y h
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := (hVmem _).mp h
      simpa [map_mul, map_inv] using this
    have hA : mk (πo g1) = mk a := by rw [← e1']; exact eqmk _ _ hg1
    have hB : mk (πo g2) = mk b := by rw [← e2']; exact eqmk _ _ hg2
    have hrelq : (mk a)⁻¹ * mk b * mk a = mk b ^ q N := by
      have hk1 : (g1⁻¹ * g2 * g1) ⁻¹ * g2 ^ q N ∈ V.toSubgroup := by
        apply hkV
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, map_pow, e1, e2, hrel N]
        group
      have := eqmk _ _ hk1
      simp only [map_mul, map_inv, map_pow, hA, hB] at this
      exact this
    have hW'ex : ∃ W' : OpenNormalSubgroup (Γ N), ∀ x, π N x ∈ W'.toSubgroup → x ∈ V.toSubgroup := by
      have hVc : IsClosed ((V.toSubgroup : Set Ph)ᶜ) := V.toOpenSubgroup.isOpen.isClosed_compl
      have hcm : IsClosedMap (π N) := (hπ N).1.isClosedMap
      have hS : IsOpen ((π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ) := (hcm _ hVc).isOpen_compl
      have h1S : (1 : Γ N) ∈ (π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ := by
        rintro ⟨x, hx, hx1⟩
        exact hx (hkV (MonoidHom.mem_ker.mpr hx1))
      obtain ⟨W', hW'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1S
      refine ⟨W', fun x hx => ?_⟩
      by_contra hxV
      exact hW' hx ⟨x, hxV, rfl⟩
    obtain ⟨W', hW'⟩ := hW'ex
    obtain ⟨e, he⟩ := hlw N W'
    have hbe : mk b ^ l ^ e = 1 := by
      have h3 : g2 ^ l ^ e ∈ V.toSubgroup := hW' _ (by rw [map_pow, e2]; exact he)
      have h' := eqmk 1 (g2 ^ l ^ e) (by simpa using h3)
      simp only [map_one, map_pow, hB] at h'
      exact h'.symm
    have hbn : mk b ^ W.toSubgroup.index = 1 := by
      rw [← map_pow, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact W.toSubgroup.pow_index_mem b
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hbe)
    have hc1 : l ^ c ≤ W.toSubgroup.index := by
      rw [← hc]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hbn)
    have hc2 : c < l ^ c := Nat.lt_pow_self hl.one_lt
    have hdiv : orderOf (mk b) ∣ l ^ N := by
      rw [hc]
      exact pow_dvd_pow l (by omega)
    have hbq : mk b ^ q N = mk b := by
      have h4 : q N ≡ 1 [MOD orderOf (mk b)] := Nat.ModEq.of_dvd hdiv (hq N)
      simpa using pow_eq_pow_iff_modEq.mpr h4
    have hcomm : mk a * mk b = mk b * mk a := by
      rw [hbq] at hrelq
      calc mk a * mk b = mk a * ((mk a)⁻¹ * mk b * mk a) := by rw [hrelq]
        _ = mk b * mk a := by group
    have h5 : mk (a * b) = mk (b * a) := by simp only [map_mul, hcomm]
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h5
    exact h5
  by_contra hne
  have hx1 : (a * b)⁻¹ * (b * a) ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := (a * b)⁻¹ * (b * a))) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EltLim
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.elt_lim :
    ∀ (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (a : ∀ N, Γ N), (∀ N, Function.Surjective (π N)) → ∃ b : B, ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b := by
  intro Ph B _ _ _ _ _ _ Γ _ π πo U a hπ
  choose g hg using fun N => hπ N (a N)
  obtain ⟨b, hb⟩ := (exists_lim_elt Ph ℕ U fun N => (π N).ker).1 g
  refine ⟨πo b, fun V => (hb V).mono fun N h => ⟨g N, b, hg N, rfl, ?_⟩⟩
  simpa using V.toSubgroup.inv_mem h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.InLim
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_tendsto_ultrafilter_of_compact {X : Type} [TopologicalSpace X] [CompactSpace X] (U : Ultrafilter ℕ) (a : ℕ → X) :
    ∃ x, Tendsto a (U : Filter ℕ) (nhds x) := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (U.map a) (by simp)
  exact ⟨x, by rwa [Ultrafilter.coe_map] at hx⟩

private theorem inv_mul_mem_limKer_of_tendsto_of_eventually_eq {Ph : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    {Γ : ℕ → Type} [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (U : Ultrafilter ℕ)
    (a b : ℕ → Ph) (x y : Ph) (ha : Tendsto a (U : Filter ℕ) (nhds x))
    (hb : Tendsto b (U : Filter ℕ) (nhds y))
    (hab : ∀ᶠ N in (U : Filter ℕ), π N (a N) = π N (b N)) :
    x⁻¹ * y ∈ limKer (U : Filter ℕ) (fun N => (π N).ker) := by
  rw [mem_limKer]
  intro O
  have hO : ((O.toOpenSubgroup : Subgroup Ph) : Set Ph) ∈ nhds (1 : Ph) :=
    O.toOpenSubgroup.isOpen.mem_nhds O.toOpenSubgroup.one_mem
  have h1 : Tendsto (fun N => x⁻¹ * a N) (U : Filter ℕ) (nhds 1) := by
    simpa using (tendsto_const_nhds (x := x⁻¹)).mul ha
  have h2 : Tendsto (fun N => (b N)⁻¹ * y) (U : Filter ℕ) (nhds 1) := by
    simpa using hb.inv.mul (tendsto_const_nhds (x := y))
  filter_upwards [h1 hO, h2 hO, hab] with N h1N h2N hN
  have e : x⁻¹ * y = (x⁻¹ * a N) * ((a N)⁻¹ * b N) * ((b N)⁻¹ * y) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right h1N)
    (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right h2N)
  rw [MonoidHom.mem_ker, map_mul, map_inv, hN, inv_mul_cancel]

private theorem exists_eventually_eq_of_eventually_mem_finite {β : Type} (U : Ultrafilter ℕ) (g : ℕ → β) (A : Set β) (hA : A.Finite)
    (hg : ∀ᶠ N in (U : Filter ℕ), g N ∈ A) : ∃ c ∈ A, ∀ᶠ N in (U : Filter ℕ), g N = c := by
  have h : (⋃ c ∈ A, {N | g N = c}) ∈ (U : Filter ℕ) := by
    filter_upwards [hg] with N hN
    exact Set.mem_biUnion hN rfl
  exact (Ultrafilter.finite_biUnion_mem_iff hA).1 h

private theorem continuous_section_quotient_of_ker_le_open {Ph G : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    [CompactSpace Ph] [Group G] [TopologicalSpace G] [T2Space G] (π : Ph →* G) (hπ : Continuous π)
    (σ : G → Ph) (hσ : ∀ γ, π (σ γ) = γ) (S : Subgroup Ph) (hS : IsOpen (S : Set Ph))
    (hk : π.ker ≤ S) : Continuous (fun γ => (σ γ : Ph ⧸ S)) := by
  haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hS
  have hmk : Continuous (QuotientGroup.mk : Ph → Ph ⧸ S) := continuous_quot_mk
  have key : ∀ s : Set (Ph ⧸ S), (fun γ => (σ γ : Ph ⧸ S)) ⁻¹' s =
      π '' ((QuotientGroup.mk : Ph → Ph ⧸ S) ⁻¹' s) := by
    intro s
    ext γ
    constructor
    · intro h
      exact ⟨σ γ, h, hσ γ⟩
    · rintro ⟨a, ha, rfl⟩
      have e : (σ (π a) : Ph ⧸ S) = (a : Ph ⧸ S) := by
        rw [QuotientGroup.eq]
        apply hk
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
      simp only [Set.mem_preimage, e]
      exact ha
  rw [continuous_discrete_rng]
  intro z
  have hc : IsClosed (π '' ((QuotientGroup.mk : Ph → Ph ⧸ S) ⁻¹' {z}ᶜ)) :=
    hπ.isClosedMap _ ((isClosed_discrete ({z}ᶜ : Set (Ph ⧸ S))).preimage hmk)
  rw [← key, Set.preimage_compl] at hc
  exact isClosed_compl_iff.1 hc

private theorem mul_one_sub_add_psi_eq_of_conj {Ph Y : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    [CompactSpace Ph] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    {Γ : ℕ → Type} [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, T2Space (Γ N)]
    (π : ∀ N, Ph →* Γ N) (hπ : ∀ N, Continuous (π N))
    (σ : ∀ N, Γ N → Ph) (hσ : ∀ N γ, π N (σ N γ) = γ)
    (U : Ultrafilter ℕ) (P : Subgroup Y) [P.Normal] (f : ∀ N, Y →* Γ N)
    (hP : TopFG (Y ⧸ P)) (hf : ∀ N, Continuous (f N) ∧ P ≤ (f N).ker)
    (V : OpenNormalSubgroup Ph) :
    ∃ S : Subgroup Ph, IsOpen (S : Set Ph) ∧ ∃ c : Y → Ph ⧸ S, Continuous c ∧
      ∀ᶠ N in (U : Filter ℕ), (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) = S ∧
        ∀ y, ((σ N (f N y) : Ph) : Ph ⧸ S) = c y := by
  set W : Subgroup Ph := (V.toOpenSubgroup : Subgroup Ph) with hW
  have hWo : IsOpen (W : Set Ph) := V.toOpenSubgroup.isOpen
  haveI : Finite (Ph ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  have hmem : ∀ S : Subgroup Ph, W ≤ S → ∀ x : Ph,
      x ∈ S ↔ (x : Ph ⧸ W) ∈ (QuotientGroup.mk : Ph → Ph ⧸ W) '' (S : Set Ph) := by
    intro S hS x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨s, hs, he⟩
      rw [QuotientGroup.eq] at he
      have e : x = s * (s⁻¹ * x) := by group
      rw [e]
      exact S.mul_mem hs (hS he)
  have hA1 : {S : Subgroup Ph | W ≤ S}.Finite := by
    apply Set.Finite.of_finite_image (f := fun S : Subgroup Ph =>
      (QuotientGroup.mk : Ph → Ph ⧸ W) '' (S : Set Ph)) (Set.toFinite _)
    intro S1 h1 S2 h2 he
    ext x
    rw [hmem S1 h1, hmem S2 h2]
    simp only at he
    rw [he]
  obtain ⟨S, hWS, hS⟩ := exists_eventually_eq_of_eventually_mem_finite U (fun N => (π N).ker ⊔ W) _ hA1
    (Filter.Eventually.of_forall fun N => show W ≤ (π N).ker ⊔ W from le_sup_right)
  have hSo : IsOpen (S : Set Ph) := Subgroup.isOpen_mono hWS hWo
  obtain ⟨N0, hN0⟩ := hS.exists
  haveI hSn : S.Normal := by
    rw [← hN0]
    infer_instance
  haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hSo
  haveI : Finite (Ph ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  have hΦ := (finite_hom_of_topFG (Y ⧸ P) hP).1 (Ph ⧸ S)
  set A2 : Set (Y → Ph ⧸ S) := {φ | Continuous φ ∧
    ∃ θ ∈ {θ : Y ⧸ P →* Ph ⧸ S | IsOpen (θ.ker : Set (Y ⧸ P))},
      φ = fun y : Y => θ (y : Y ⧸ P)} with hA2
  have hA2f : A2.Finite := by
    apply (hΦ.image (fun θ : Y ⧸ P →* Ph ⧸ S => fun y : Y => θ (y : Y ⧸ P))).subset
    rintro φ ⟨-, θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  have hg2 : ∀ᶠ N in (U : Filter ℕ), (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) ∈ A2 := by
    filter_upwards [hS] with N hN
    have kle : (π N).ker ≤ S := hN ▸ le_sup_left
    have hcont : Continuous (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) :=
      (continuous_section_quotient_of_ker_le_open (π N) (hπ N) (σ N) (hσ N) S hSo kle).comp (hf N).1
    refine ⟨hcont, ?_⟩
    let φY : Y →* Ph ⧸ S := MonoidHom.mk' (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) (by
      intro a b
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply kle
      simp [MonoidHom.mem_ker, hσ])
    have hPle : P ≤ φY.ker := by
      intro p hp
      rw [MonoidHom.mem_ker]
      show ((σ N (f N p) : Ph) : Ph ⧸ S) = 1
      rw [(hf N).2 hp, QuotientGroup.eq_one_iff]
      apply kle
      simp [MonoidHom.mem_ker, hσ]
    refine ⟨QuotientGroup.lift P φY hPle, ?_, rfl⟩
    have hpre : (QuotientGroup.mk : Y → Y ⧸ P) ⁻¹' ((QuotientGroup.lift P φY hPle).ker : Set (Y ⧸ P))
        = (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) ⁻¹' {1} := by
      ext y
      simp [MonoidHom.mem_ker, φY]
    have ho := hcont.isOpen_preimage _ (isOpen_discrete ({1} : Set (Ph ⧸ S)))
    rw [← hpre] at ho
    have ho2 := (QuotientGroup.isOpenMap_coe (N := P)) _ ho
    rwa [Set.image_preimage_eq _ QuotientGroup.mk_surjective] at ho2
  obtain ⟨c, hcA, hc⟩ := exists_eventually_eq_of_eventually_mem_finite U _ A2 hA2f hg2
  refine ⟨S, hSo, c, hcA.1, ?_⟩
  filter_upwards [hS, hc] with N h1 h2
  exact ⟨h1, fun y => congrFun h2 y⟩

theorem UpperTheory.V.Pa.in_lim :
    ∀ (Ph Y : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] (Γ : ℕ → Type) [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, IsTopologicalGroup (Γ N)] [∀ N, CompactSpace (Γ N)] [∀ N, TotallyDisconnectedSpace (Γ N)] (π : ∀ N, Ph →* Γ N) (U : Ultrafilter ℕ) (P : Subgroup Y) [P.Normal] (f : ∀ N, Y →* Γ N), (∀ N, Continuous (π N) ∧ Function.Surjective (π N)) → TopFG (Y ⧸ P) → (∀ N, Continuous (f N) ∧ P ≤ (f N).ker) → ∃ F : Y →* Ph ⧸ limKer (U : Filter ℕ) (fun N => (π N).ker), Continuous F ∧ ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), ∀ y, Close (π N) (QuotientGroup.mk' (limKer (U : Filter ℕ) fun N => (π N).ker)) V.toSubgroup (f N y) (F y) := by
  intro Ph Y _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ π U P _ f hπ hP hf
  haveI : ∀ N, T2Space (Γ N) := fun N => inferInstance
  choose σ hσ using fun N (γ : Γ N) => (hπ N).2 γ
  choose h hh using fun y => exists_tendsto_ultrafilter_of_compact U (fun N => σ N (f N y))
  have hmul : ∀ a b, ((h (a * b) : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) =
      (h a : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) * (h b) := by
    intro a b
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine inv_mul_mem_limKer_of_tendsto_of_eventually_eq π U _ _ _ _ (hh (a * b)) ((hh a).mul (hh b)) ?_
    filter_upwards with N
    simp [hσ, map_mul]
  refine ⟨MonoidHom.mk' (fun y => (h y : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker)) hmul, ?_, ?_⟩
  · apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro W hW
    have hmkc : Continuous (QuotientGroup.mk : Ph → Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) :=
      continuous_quot_mk
    have h1 : (QuotientGroup.mk : Ph → Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) ⁻¹' W ∈ nhds (1 : Ph) :=
      hmkc.continuousAt.preimage_mem_nhds (by rw [QuotientGroup.mk_one]; exact hW)
    obtain ⟨t, ht, hto, ht1⟩ := mem_nhds_iff.1 h1
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto ht1
    obtain ⟨S, hSo, c, hc, hev⟩ := mul_one_sub_add_psi_eq_of_conj π (fun N => (hπ N).1) σ hσ U P f hP hf V
    haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hSo
    rw [mem_nhds_iff]
    refine ⟨c ⁻¹' {c 1}, ?_, hc.isOpen_preimage _ (isOpen_discrete _), rfl⟩
    intro y hy
    have hin : ∀ᶠ N in (U : Filter ℕ),
        σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) := by
      filter_upwards [hev] with N hN
      obtain ⟨hN, hcN⟩ := hN
      have e1 : ((σ N (f N y) : Ph) : Ph ⧸ S) = ((σ N (f N 1) : Ph) : Ph ⧸ S) := by
        rw [hcN y, hcN 1]
        exact hy
      rw [QuotientGroup.eq] at e1
      have hk1 : σ N (f N 1) ∈ (π N).ker := by simp [MonoidHom.mem_ker, hσ]
      have e2 : σ N (f N y) = σ N (f N 1) * ((σ N (f N 1))⁻¹ * σ N (f N y)) := by group
      rw [e2]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hk1) ?_
      rw [hN]
      simpa using S.inv_mem e1
    have hdec : ∀ N, ∃ v ∈ (V.toOpenSubgroup : Subgroup Ph),
        σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) →
          σ N (f N y) * v⁻¹ ∈ (π N).ker := by
      intro N
      by_cases hm : σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph)
      · rw [← SetLike.mem_coe, Subgroup.mul_normal] at hm
        obtain ⟨k, hk, v, hv, hkv⟩ := hm
        refine ⟨v, hv, fun _ => ?_⟩
        rw [← hkv, mul_inv_cancel_right]
        exact hk
      · exact ⟨1, one_mem _, fun h' => absurd h' hm⟩
    choose v hvV hv using hdec
    obtain ⟨w, hw⟩ := exists_tendsto_ultrafilter_of_compact U v
    have hwV : w ∈ (V.toOpenSubgroup : Subgroup Ph) :=
      V.toOpenSubgroup.isClosed.mem_of_tendsto hw (Filter.Eventually.of_forall hvV)
    have hlim := inv_mul_mem_limKer_of_tendsto_of_eventually_eq π U (fun N => σ N (f N y) * (v N)⁻¹) (fun _ => 1) (h y * w⁻¹) 1
      ((hh y).mul hw.inv) tendsto_const_nhds (by
        filter_upwards [hin] with N hN
        rw [map_one]
        exact (MonoidHom.mem_ker).1 (hv N hN))
    have hm' : h y * w⁻¹ ∈ limKer (U : Filter ℕ) (fun N => (π N).ker) := by
      simpa using inv_mem hlim
    have hconj := (limKer_normal (U : Filter ℕ) (fun N => (π N).ker)).conj_mem _ hm' w⁻¹
    have e3 : w⁻¹ * (h y * w⁻¹) * w⁻¹⁻¹ = w⁻¹ * h y := by group
    rw [e3] at hconj
    show ((h y : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) ∈ W
    have e4 : ((h y : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) =
        ((w : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hconj
    rw [e4]
    exact ht (hV hwV)
  · intro V
    obtain ⟨S, hSo, c, hc, hev⟩ := mul_one_sub_add_psi_eq_of_conj π (fun N => (hπ N).1) σ hσ U P f hP hf V
    have hVS : ∀ᶠ N in (U : Filter ℕ), (V.toOpenSubgroup : Subgroup Ph) ≤ S := by
      filter_upwards [hev] with N hN
      rw [← hN.1]
      exact le_sup_right
    have hcy : ∀ y, c y = ((h y : Ph) : Ph ⧸ S) := by
      intro y
      have hO : ((V.toOpenSubgroup : Subgroup Ph) : Set Ph) ∈ nhds (1 : Ph) :=
        V.toOpenSubgroup.isOpen.mem_nhds V.toOpenSubgroup.one_mem
      have ht : Tendsto (fun N => (σ N (f N y))⁻¹ * h y) (U : Filter ℕ) (nhds 1) := by
        simpa using (hh y).inv.mul (tendsto_const_nhds (x := h y))
      obtain ⟨N, ⟨-, hN⟩, hle, hmemN⟩ := (hev.and (hVS.and (ht hO))).exists
      rw [← hN y, QuotientGroup.eq]
      exact hle hmemN
    filter_upwards [hev] with N hN
    obtain ⟨hN, hcN⟩ := hN
    intro y
    have e1 : ((σ N (f N y) : Ph) : Ph ⧸ S) = ((h y : Ph) : Ph ⧸ S) := by rw [hcN y, hcy y]
    rw [QuotientGroup.eq, ← hN, ← SetLike.mem_coe, Subgroup.mul_normal] at e1
    obtain ⟨k, hk, v, hv, hkv⟩ := e1
    refine ⟨σ N (f N y) * k, h y, ?_, rfl, ?_⟩
    · rw [map_mul, hσ, (MonoidHom.mem_ker).1 hk, mul_one]
    · have e : (σ N (f N y) * k)⁻¹ * h y = k⁻¹ * ((σ N (f N y))⁻¹ * h y) := by group
      rw [e, ← hkv, inv_mul_cancel_left]
      exact hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlSub
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_sub :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H K : Subgroup Γ) [H.Normal] [K.Normal], IsOpen (K : Set Γ) → H ≤ K → ∀ U : OpenNormalSubgroup K, (∀ h : K, (h : Γ) ∈ H → ∃ e : ℕ, h ^ l ^ e ∈ U) → ∀ g : K, (g : Γ) ∈ PL l H → g ∈ U := by
  intro l _ Γ _ _ _ _ _ H K _ _ hK hHK U hU g hg
  have hl : l.Prime := Fact.out
  have hKc : IsClosed (K : Set Γ) := OpenSubgroup.isClosed ⟨K, hK⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  haveI : U.toSubgroup.FiniteIndex := U.toOpenSubgroup.toSubgroup.finiteIndex_of_finite_quotient
  haveI : U.toSubgroup.Normal := U.isNormal'
  have hn0 : U.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have lem : ∀ k : K, (k : Γ) ∈ H → k ^ l ^ U.toSubgroup.index ∈ U.toSubgroup := by
    intro k hk
    obtain ⟨e, he⟩ := hU k hk
    set q : K ⧸ U.toSubgroup := (QuotientGroup.mk k : K ⧸ U.toSubgroup)
    have hqe : q ^ l ^ e = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact he
    have hqn : q ^ U.toSubgroup.index = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact U.toSubgroup.pow_index_mem k
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hqe)
    have h1 : l ^ a ≤ U.toSubgroup.index := by
      rw [← ha]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hqn)
    have h2 : a < l ^ a := Nat.lt_pow_self hl.one_lt
    have h3 : orderOf q ∣ l ^ U.toSubgroup.index := by
      rw [ha]
      exact pow_dvd_pow l (by omega)
    have hq : q ^ l ^ U.toSubgroup.index = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
    exact hq
  let O : Subgroup Γ := U.toSubgroup.map K.subtype
  have hOo : IsOpen (O : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hK.isOpenMap_subtype_val _ U.toOpenSubgroup.isOpen
  have hOc : IsClosed (O : Set Γ) := OpenSubgroup.isClosed ⟨O, hOo⟩
  haveI : Finite (Γ ⧸ O) := O.quotient_finite_of_isOpen hOo
  haveI : O.FiniteIndex := O.finiteIndex_of_finite_quotient
  have hCo : IsOpen (O.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.normalCore_isClosed hOc)
  let C : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨O.normalCore, hCo⟩
      isNormal' := O.normalCore_normal }
  have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ C.toOpenSubgroup := by
    intro h hh
    refine ⟨U.toSubgroup.index, ?_⟩
    show ∀ b : Γ, b * h ^ l ^ U.toSubgroup.index * b⁻¹ ∈ O
    intro b
    rw [← conj_pow]
    have hbH : b * h * b⁻¹ ∈ H := ‹H.Normal›.conj_mem h hh b
    have hm := lem ⟨b * h * b⁻¹, hHK hbH⟩ hbH
    exact Subgroup.mem_map.mpr ⟨_, hm, rfl⟩
  have hgC : (g : Γ) ∈ C.toOpenSubgroup := by
    unfold PL at hg
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg C) hcond
  have hgO : (g : Γ) ∈ O := O.normalCore_le hgC
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgO
  have : x = g := Subtype.ext hxg
  rw [← this]
  exact hx
end

