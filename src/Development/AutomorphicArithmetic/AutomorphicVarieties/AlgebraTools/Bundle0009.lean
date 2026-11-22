import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimOut
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_lim_hom_out :
    ∀ (G Z ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z], TopFG G → ∀ (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] (f : ι → G →* Z),
      (∀ i, Continuous (f i)) → (∀ i, K i ≤ (f i).ker) →
      ∃ F : G →* Z, Continuous F ∧ limKer (U : Filter ι) K ≤ F.ker ∧
        (∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup) ∧
        ((∀ i, Function.Surjective (f i)) → Function.Surjective F) := by
  intro G Z ι _ _ _ _ _ _ _ _ _ _ hG U K _ f hf hK
  obtain ⟨s, hsfin, hsgen⟩ := hG
  obtain ⟨F0, hF0⟩ : ∃ F0 : G → Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F0 g)) := by
    refine ⟨fun g => (U.map (fun i => f i g)).lim, fun g => ?_⟩
    have h := (U.map (fun i => f i g)).le_nhds_lim
    rw [Ultrafilter.coe_map] at h
    exact h
  have hone : F0 1 = 1 :=
    tendsto_nhds_unique (hF0 1) (by simp only [map_one]; exact tendsto_const_nhds)
  have hmul : ∀ a b, F0 (a * b) = F0 a * F0 b := fun a b =>
    tendsto_nhds_unique (hF0 (a * b)) (by simp only [map_mul]; exact (hF0 a).mul (hF0 b))
  obtain ⟨F, hF⟩ : ∃ F : G →* Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F g)) :=
    ⟨{ toFun := F0, map_one' := hone, map_mul' := hmul }, hF0⟩
  have agree : ∀ (V : OpenNormalSubgroup Z) (i j : ι),
      (∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup) → (∀ x ∈ s, (F x)⁻¹ * f j x ∈ V.toSubgroup) →
      ∀ g, (f j g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V i j hi hj g
    let H : Subgroup G :=
      { carrier := {g | (f j g)⁻¹ * f i g ∈ V.toSubgroup}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          have := V.toSubgroup.mul_mem (V.isNormal'.conj_mem _ ha (f j b)⁻¹) hb
          convert this using 1
          group
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq, map_inv] at *
          have := V.isNormal'.conj_mem _ (V.toSubgroup.inv_mem ha) (f j a)
          convert this using 1
          group }
    have hHc : IsClosed (H : Set G) :=
      V.toOpenSubgroup.isClosed.preimage (((hf j).inv).mul (hf i))
    have hsH : Subgroup.closure s ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      show (f j x)⁻¹ * f i x ∈ V.toSubgroup
      have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem (hj x hx)) (hi x hx)
      convert this using 1
      group
    have hg : g ∈ (Subgroup.closure s).topologicalClosure := by
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, hsgen.closure_eq]
      trivial
    exact Subgroup.topologicalClosure_minimal _ hsH hHc hg
  have key : ∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V
    have hs : ∀ᶠ i in (U : Filter ι), ∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup := by
      refine (Filter.eventually_all_finite hsfin).2 (fun x _ => ?_)
      have hopen : IsOpen {z : Z | (F x)⁻¹ * z ∈ V.toSubgroup} :=
        V.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)
      exact (hF x).eventually (hopen.mem_nhds (by simp))
    obtain ⟨j, hj⟩ := hs.exists
    filter_upwards [hs] with i hi g
    have hC : IsClosed {z : Z | (f j g)⁻¹ * z ∈ V.toSubgroup} :=
      V.toOpenSubgroup.isClosed.preimage (continuous_mul_left _)
    have h1 : (f j g)⁻¹ * F g ∈ V.toSubgroup :=
      hC.mem_of_tendsto (hF g) (hs.mono fun k hk => agree V k j hk hj g)
    have h2 := agree V i j hi hj g
    have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem h1) h2
    convert this using 1
    group
  have hFc : Continuous F := by
    apply continuous_of_continuousAt_one F
    rw [ContinuousAt, map_one]
    intro W hW
    obtain ⟨t, htW, hto, h1t⟩ := mem_nhds_iff.1 hW
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto h1t
    obtain ⟨i, hi⟩ := (key V).exists
    have hmem : {g : G | f i g ∈ V.toSubgroup} ∈ nhds (1 : G) :=
      (V.toOpenSubgroup.isOpen.preimage (hf i)).mem_nhds (by simp)
    refine Filter.mem_map.2 (Filter.mem_of_superset hmem (fun g hg => ?_))
    apply htW
    apply hV
    have := V.toSubgroup.mul_mem hg (V.toSubgroup.inv_mem (hi g))
    change F g ∈ V.toSubgroup
    convert this using 1
    group
  refine ⟨F, hFc, ?_, key, ?_⟩
  · intro g hg
    rw [MonoidHom.mem_ker]
    have hall : ∀ V : OpenNormalSubgroup Z, F g ∈ V.toSubgroup := by
      intro V
      let O : OpenNormalSubgroup G :=
        { toSubgroup := V.toSubgroup.comap F
          isOpen' := V.toOpenSubgroup.isOpen.preimage hFc
          isNormal' := V.isNormal'.comap F }
      rw [mem_limKer] at hg
      obtain ⟨i, hi1, hi2⟩ := ((hg O).and (key V)).exists
      have hle : K i ⊔ (O.toOpenSubgroup : Subgroup G) ≤ V.toSubgroup.comap (f i) := by
        refine sup_le ?_ ?_
        · intro x hx
          have hx' := hK i hx
          rw [MonoidHom.mem_ker] at hx'
          show f i x ∈ V.toSubgroup
          rw [hx']
          exact one_mem _
        · intro x hx
          have hx' : F x ∈ V.toSubgroup := hx
          show f i x ∈ V.toSubgroup
          have := V.toSubgroup.mul_mem hx' (hi2 x)
          convert this using 1
          group
      have hfg : f i g ∈ V.toSubgroup := hle hi1
      have := V.toSubgroup.mul_mem hfg (V.toSubgroup.inv_mem (hi2 g))
      convert this using 1
      group
    by_contra hne
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton (x := F g)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    exact hV (hall V) rfl
  · intro hsurj z
    have hcl : IsClosed (Set.range F) := (isCompact_range hFc).isClosed
    have hz : z ∈ closure (Set.range F) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      have hW : (fun y => z * y) ⁻¹' t ∈ nhds (1 : Z) :=
        (continuous_mul_left z).continuousAt.preimage_mem_nhds (by rwa [mul_one])
      obtain ⟨u, huW, huo, h1u⟩ := mem_nhds_iff.1 hW
      obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one huo h1u
      obtain ⟨i, hi⟩ := (key V).exists
      obtain ⟨g, hg⟩ := hsurj i z
      refine ⟨F g, ?_, g, rfl⟩
      have hv : z⁻¹ * F g ∈ V.toSubgroup := by
        have := V.toSubgroup.inv_mem (hi g)
        rw [hg] at this
        convert this using 1
        group
      have := huW (hV hv)
      simpa using this
    rw [hcl.closure_eq] at hz
    exact hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LocFactor
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem complete_of_finite (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have h0 : IsAdicComplete (maximalIdeal R) R' := GlobalTheory.isAdicComplete_of_finite _ R'
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 h0.toIsPrecomplete)
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

theorem UpperTheory.V.AlgebraTools.local_factor :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (n : Ideal A) [n.IsMaximal],
      Function.Surjective (algebraMap A (Localization.AtPrime n)) ∧ Module.Finite R (Localization.AtPrime n) ∧
      IsLocalHom (algebraMap R (Localization.AtPrime n)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime n)) (Localization.AtPrime n) ∧
      (Module.Free R A → Module.Free R (Localization.AtPrime n)) ∧
      (∃ e : A, IsIdempotentElem e ∧ (∀ n' : Ideal A, n'.IsMaximal → (e ∉ n' ↔ n' = n)) ∧
        RingHom.ker (algebraMap A (Localization.AtPrime n)) = Ideal.span {1 - e}) ∧
      ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : A →+* C), (IsLocalRing.maximalIdeal C).comap f = n →
        ∃ g : Localization.AtPrime n →+* C, g.comp (algebraMap A _) = f := by
  intro R _ _ _ _ A _ _ _ n hn
  letI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  have hfin : Module.Finite R (Localization.AtPrime n) := GlobalTheory.finite_localization_of_henselian R n
  refine ⟨GlobalTheory.surjective_algebraMap_localization_of_henselian R n, hfin, ⟨fun a ha => ?_⟩,
    complete_of_finite R _, fun hF => ?_, ?_, fun C _ _ f hf => ?_⟩
  · by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal R := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal (Localization.AtPrime n)),
      Ideal.mem_comap] at h1
    exact h1 ha
  · haveI : Module.Flat A (Localization.AtPrime n) := IsLocalization.flat _ n.primeCompl
    haveI : Module.Flat R (Localization.AtPrime n) := Module.Flat.trans R A _
    exact Module.free_of_flat_of_isLocalRing
  · obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian R n
    refine ⟨e, he, H, le_antisymm (fun x hx => ?_) ?_⟩
    · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.primeCompl _ x).1 hx
      have heq : e ∉ n := (H n hn).2 rfl
      have hu : IsUnit (e * s + (1 - e)) := by
        by_contra h
        obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
        by_cases hen : e ∈ m
        · rw [Submodule.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hen),
            GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he] at hmem
          exact hmem hen
        · rw [Submodule.add_mem_iff_left _
              ((GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he m).2 hen),
            (H m hm).1 hen] at hmem
          exact (hn.isPrime.mem_or_mem hmem).elim heq s.2
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine Ideal.mem_span_singleton'.2 ⟨v * x, ?_⟩
      linear_combination x * hv - v * e * hs
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      exact ((IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units _
        (⟨e, (H n hn).2 rfl⟩ : n.primeCompl))).1 (he.map _)).symm
  · have hu : ∀ y : n.primeCompl, IsUnit (f y) := fun y => by
      by_contra h
      have h1 : (y : A) ∈ (IsLocalRing.maximalIdeal C).comap f := h
      rw [hf] at h1
      exact y.2 h1
    exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProLUnits
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.pow_mem_of_sub_one_mem :
    ∀ (l : ℕ) (E : Type) [Ring E] (J : TwoSidedIdeal E), (l : E) ∈ J → ∀ (j : ℕ) (x : E), x - 1 ∈ J →
      x ^ l ^ j - 1 ∈ (J.asIdeal : Submodule E E) ^ (j + 1) := by
  intro l E _ J hl j x hx
  have key : ∀ y : E, y - 1 ∈ J → ∀ n : ℕ, y ^ n - 1 ∈ J := by
    intro y hy n
    rw [← geom_sum_mul]
    exact J.mul_mem_left _ _ hy
  induction j with
  | zero =>
    rw [pow_zero, pow_one, zero_add, Submodule.pow_one]
    exact TwoSidedIdeal.mem_asIdeal.mpr hx
  | succ j ih =>
    have hy : x ^ l ^ j - 1 ∈ J := key x hx _
    rw [pow_succ, pow_mul, ← mul_geom_sum, Submodule.pow_succ]
    refine Submodule.mul_mem_mul ih ?_
    rw [TwoSidedIdeal.mem_asIdeal]
    have hs : ∑ i ∈ Finset.range l, (x ^ l ^ j) ^ i
        = ∑ i ∈ Finset.range l, ((x ^ l ^ j) ^ i - 1) + (l : E) := by
      simp [Finset.sum_sub_distrib]
    rw [hs]
    exact J.add_mem (sum_mem fun i _ => key _ hy i) hl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.totallyDisconnected_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (K : Subgroup G) [K.Normal], IsClosed (K : Set G) →
      TotallyDisconnectedSpace (G ⧸ K) ∧ (∀ g : G, (∀ O : OpenNormalSubgroup G, g ∈ K ⊔ O.toSubgroup) → g ∈ K) := by
  intro G _ _ _ _ _ N _ hN
  refine ⟨?_, fun x hx => ?_⟩
  · rw [totallyDisconnectedSpace_iff_connectedComponent_one]
    refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    by_contra hx
    have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
    have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
    have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
    obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
    exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
  · by_contra hx'
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    have h := hx U
    rw [sup_comm] at h
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp h
    refine hU (U.toSubgroup.inv_mem hy) ?_
    rw [← hyz]
    simpa using hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResMap
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem pq_iff {l : ℕ} {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

theorem UpperTheory.V.AlgebraTools.proLRes_map :
    ∀ (l : ℕ) [Fact l.Prime] (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (f : G →* H), Continuous f → Function.Surjective f →
      (proLRes l G).map f = proLRes l H := by
  intro l _ G H _ _ _ _ _ _ _ _ _ _ f hf hs
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    rw [Subgroup.mem_comap, mem_proLRes]
    intro N hN
    rw [pq_iff] at hN
    let M : OpenNormalSubgroup G :=
      { toOpenSubgroup := OpenSubgroup.comap f hf N.toOpenSubgroup
        isNormal' := Subgroup.Normal.comap inferInstance f }
    haveI : (M.toOpenSubgroup : Subgroup G).Normal := M.isNormal'
    have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro x
      obtain ⟨k, hk⟩ := hN (f x)
      refine ⟨k, ?_⟩
      show x ^ l ^ k ∈ OpenSubgroup.comap f hf N.toOpenSubgroup
      rw [OpenSubgroup.mem_comap, map_pow]
      exact hk
    have := (mem_proLRes.mp hg) M hM
    exact (OpenSubgroup.mem_comap (hf := hf)).mp this
  · intro h hh
    rw [mem_proLRes] at hh
    let t : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} → Set G :=
      fun N => f ⁻¹' {h} ∩ (N.1.toOpenSubgroup : Set G)
    let T0 : OpenNormalSubgroup G := { toOpenSubgroup := ⊤, isNormal' := by simpa using Subgroup.normal_top }
    haveI : (T0.toOpenSubgroup : Subgroup G).Normal := T0.isNormal'
    have htop : IsPGroup l (G ⧸ (T0.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro g
      refine ⟨0, ?_⟩
      show g ^ l ^ 0 ∈ (⊤ : OpenSubgroup G)
      simp
    haveI : Nonempty {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} := ⟨⟨_, htop⟩⟩
    have hcl : ∀ i, IsClosed (t i) := fun i =>
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (fun x1 x2 => x1 ⊇ x2) t := by
      intro i j
      have hK : IsPGroup l (G ⧸ ((i.1 ⊓ j.1).toOpenSubgroup : Subgroup G)) := by
        rw [pq_iff]
        intro g
        obtain ⟨a, ha⟩ := (pq_iff _).mp i.2 g
        obtain ⟨b, hb⟩ := (pq_iff _).mp j.2 g
        refine ⟨a + b, ?_⟩
        have e1 : g ^ l ^ (a + b) = (g ^ l ^ a) ^ l ^ b := by rw [pow_add, pow_mul]
        have e2 : g ^ l ^ (a + b) = (g ^ l ^ b) ^ l ^ a := by rw [add_comm, pow_add, pow_mul]
        have m1 : g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup : Subgroup G) := e1 ▸ pow_mem ha _
        have m2 : g ^ l ^ (a + b) ∈ (j.1.toOpenSubgroup : Subgroup G) := e2 ▸ pow_mem hb _
        show g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)
        exact OpenSubgroup.mem_inf.mpr ⟨m1, m2⟩
      refine ⟨⟨i.1 ⊓ j.1, hK⟩, ?_, ?_⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).1⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).2⟩
    have hnon : ∀ i, (t i).Nonempty := by
      intro i
      have hNcl : IsClosed ((i.1.toOpenSubgroup : Subgroup G) : Set G) := i.1.toOpenSubgroup.isClosed
      have hMcl : IsClosed (((i.1.toOpenSubgroup : Subgroup G).map f : Subgroup H) : Set H) := by
        rw [Subgroup.coe_map]
        exact hf.isClosedMap _ hNcl
      haveI : (i.1.toOpenSubgroup : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      haveI : ((i.1.toOpenSubgroup : Subgroup G).map f).FiniteIndex := by
        rw [Subgroup.finiteIndex_iff]
        intro h0
        have hd := Subgroup.index_map_dvd (i.1.toOpenSubgroup : Subgroup G) hs
        rw [h0, zero_dvd_iff] at hd
        exact (Subgroup.finiteIndex_iff.mp inferInstance) hd
      let M : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨(i.1.toOpenSubgroup : Subgroup G).map f,
            Subgroup.isOpen_of_isClosed_of_finiteIndex _ hMcl⟩
          isNormal' := Subgroup.Normal.map inferInstance f hs }
      haveI : (M.toOpenSubgroup : Subgroup H).Normal := M.isNormal'
      have hM : IsPGroup l (H ⧸ (M.toOpenSubgroup : Subgroup H)) := by
        rw [pq_iff]
        intro y
        obtain ⟨x, rfl⟩ := hs y
        obtain ⟨k, hk⟩ := (pq_iff _).mp i.2 x
        refine ⟨k, ?_⟩
        show f x ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G).map f
        exact ⟨x ^ l ^ k, hk, map_pow f x _⟩
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp (hh M hM)
      exact ⟨x, hfx, hx⟩
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon
      (fun i => (hcl i).isCompact) hcl
    rw [Set.mem_iInter] at hg
    refine ⟨g, ?_, (hg (Classical.arbitrary _)).1⟩
    rw [SetLike.mem_coe, mem_proLRes]
    intro N hN
    exact (hg ⟨N, hN⟩).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpStep
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.splitAlg_succ_equiv :
    ∀ (R : Type) [CommRing R] (n : ℕ) (P : Polynomial R), P.Monic → P.natDegree = n + 1 →
      ∃ (_ : Algebra (AdjoinRoot P) (SplitAlg P (n + 1))) (_ : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1))),
        algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 ∧
        ∃ e : SplitAlg P (n + 1) ≃ₐ[AdjoinRoot P]
            SplitAlg ((P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P))) n,
          ∀ i : Fin n, e (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root _ n i := by
  intro R _ n P hP hdeg
  have hroot0 : Polynomial.eval₂ (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) P = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, ← SplitAlg.prod_root, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  let φ : AdjoinRoot P →+* SplitAlg P (n + 1) :=
    AdjoinRoot.lift (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) hroot0
  letI alg : Algebra (AdjoinRoot P) (SplitAlg P (n + 1)) := φ.toAlgebra
  have hφ : ∀ r : R, algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (algebraMap R (AdjoinRoot P) r)
      = algebraMap R (SplitAlg P (n + 1)) r := fun r => AdjoinRoot.lift_of hroot0
  haveI tower : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1)) :=
    IsScalarTower.of_algebraMap_eq (fun r => (hφ r).symm)
  have hr0 : algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 :=
    AdjoinRoot.lift_root hroot0
  refine ⟨alg, tower, hr0, ?_⟩
  set Q := (P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) with hQ
  have hfac : P.map (algebraMap R (AdjoinRoot P)) = (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) * Q := by
    rw [hQ, eq_comm, Polynomial.mul_divByMonic_eq_iff_isRoot, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.isRoot_root P
  have hmapS : P.map (algebraMap R (SplitAlg P (n + 1)))
      = (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) 0))
        * Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    rw [IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg P (n + 1)), ← Polynomial.map_map, hfac,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hr0]
  have hg : ∏ i : Fin n, (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) i.succ))
      = Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    have h1 := SplitAlg.prod_root P (n + 1)
    rw [Fin.prod_univ_succ, hmapS] at h1
    exact (Polynomial.monic_X_sub_C _).isRegular.left h1
  let g : SplitAlg Q n →ₐ[AdjoinRoot P] SplitAlg P (n + 1) :=
    SplitAlg.lift Q n (fun i => SplitAlg.root P (n + 1) i.succ) hg
  let a : Fin (n + 1) → SplitAlg Q n :=
    Fin.cons (algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P)) (SplitAlg.root Q n)
  have hf : ∏ i, (Polynomial.X - Polynomial.C (a i)) = P.map (algebraMap R (SplitAlg Q n)) := by
    rw [Fin.prod_univ_succ]
    simp only [a, Fin.cons_zero, Fin.cons_succ]
    rw [SplitAlg.prod_root, IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg Q n), ← Polynomial.map_map,
      hfac, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  let f : SplitAlg P (n + 1) →ₐ[R] SplitAlg Q n := SplitAlg.lift P (n + 1) a hf
  have hf0 : f (SplitAlg.root P (n + 1) 0) = algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P) := by
    simp only [f, SplitAlg.lift_root, a, Fin.cons_zero]
  have hfs : ∀ i : Fin n, f (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root Q n i := by
    intro i
    simp only [f, SplitAlg.lift_root, a, Fin.cons_succ]
  have hfK : f.comp (IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg P (n + 1)))
      = IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg Q n) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom', hr0, hf0]
  let fK : SplitAlg P (n + 1) →ₐ[AdjoinRoot P] SplitAlg Q n :=
    { f with commutes' := fun k => DFunLike.congr_fun hfK k }
  have hgs : ∀ i : Fin n, g (SplitAlg.root Q n i) = SplitAlg.root P (n + 1) i.succ := by
    intro i
    exact SplitAlg.lift_root Q n _ hg i
  refine ⟨AlgEquiv.ofAlgHom fK g ?_ ?_, ?_⟩
  · apply SplitAlg.hom_ext
    intro i
    show f (g (SplitAlg.root Q n i)) = SplitAlg.root Q n i
    rw [hgs, hfs]
  · apply AlgHom.restrictScalars_injective R
    apply SplitAlg.hom_ext
    intro i
    show g (f (SplitAlg.root P (n + 1) i)) = SplitAlg.root P (n + 1) i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hf0, AlgHom.commutes, hr0]
    · rw [hfs, hgs]
  · intro i
    exact hfs i
end

