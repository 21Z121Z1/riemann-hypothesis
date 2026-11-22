import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GaloisGroupPhiCondition
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  haveI : TotallySeparatedSpace (G ⧸ N) := by
    rw [totallySeparatedSpace_iff_exists_isClopen]
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hxy : x⁻¹ * y ∉ ((ClosedSubgroup.mk N hN : ClosedSubgroup G) : Subgroup G) :=
      fun h => hab (QuotientGroup.eq.2 h)
    rw [ProfiniteGrp.closedSubgroup_eq_sInf_open (ClosedSubgroup.mk N hN), Subgroup.mem_sInf] at hxy
    push_neg at hxy
    obtain ⟨U, ⟨hUo, hNU⟩, hyU⟩ := hxy
    let W : Set G := {g | x⁻¹ * g ∈ U}
    have hWo : IsOpen W := by
      show IsOpen ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))
      exact hUo.preimage (continuous_const.mul continuous_id)
    have hWc : IsClosed W := by
      show IsClosed ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))
      exact (Subgroup.isClosed_of_isOpen U hUo).preimage (continuous_const.mul continuous_id)
    have hsat : (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W) = W := by
      ext g
      constructor
      · rintro ⟨h, hh, he⟩
        have hn := QuotientGroup.eq.1 he
        show x⁻¹ * g ∈ U
        have := U.mul_mem hh (hNU hn)
        simpa [mul_assoc] using this
      · intro hg
        exact ⟨g, hg, rfl⟩
    refine ⟨QuotientGroup.mk '' W, ⟨?_, QuotientGroup.isOpenMap_coe W hWo⟩, ⟨x, by simp [W], rfl⟩, ?_⟩
    · rw [← (QuotientGroup.isQuotientMap_mk N).isCoinducing.isClosed_preimage, hsat]
      exact hWc
    · intro hy
      have hy' : y ∈ (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W) := hy
      rw [hsat] at hy'
      exact hyU hy'
  infer_instance

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h1 : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have h2 := QuotientGroup.eq.1 h1
  simpa [mul_assoc] using h2

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  classical
  intro H hH
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have getN : ∀ W : Set Γ, IsClopen W → (1 : Γ) ∈ W →
      ∃ N : Subgroup Γ, N.Normal ∧ IsOpen (N : Set Γ) ∧ (N : Set Γ) ⊆ W := by
    intro W hW h1
    obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW h1
    exact ⟨N.toOpenSubgroup, N.isNormal', N.toOpenSubgroup.isOpen, hN⟩
  have triv : ∀ N : Subgroup Γ, N.Normal → (N : Set Γ) ⊆ H → ∀ k ∈ N, ∀ y : Γ ⧸ H, k • y = y := by
    intro N hN hNH k hk y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    show ((k * z : Γ) : Γ ⧸ H) = z
    apply QuotientGroup.eq.2
    apply hNH
    have := hN.conj_mem k⁻¹ (N.inv_mem hk) z⁻¹
    simpa [mul_assoc] using this
  have lc : ∀ {X : Type} [TopologicalSpace X] [DiscreteTopology X] (F : Γ → X) (N : Subgroup Γ),
      IsOpen (N : Set Γ) → (∀ g, ∀ k ∈ N, F (g * k) = F g) → Continuous F := by
    intro X _ _ F N hN hF
    rw [continuous_discrete_rng]
    intro b
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun k => g⁻¹ * k) ⁻¹' (N : Set Γ), ?_, ?_, ?_⟩
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
      have := hF g _ hk
      simpa [hg] using this
    · exact hN.preimage (continuous_const.mul continuous_id)
    · show g⁻¹ * g ∈ (N : Set Γ)
      simp [N.one_mem]
  let M := Γ ⧸ H → ZMod n
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  let ρ := permR (ZMod n) H
  obtain ⟨N0, hN0n, hN0o, hN0H⟩ := getN (H : Set Γ) ⟨Subgroup.isClosed_of_isOpen H hH, hH⟩ H.one_mem
  have ρmul : ∀ g, ∀ k ∈ N0, ρ (g * k) = ρ g := by
    intro g k hk
    apply LinearMap.ext
    intro f
    funext x
    show f ((g * k)⁻¹ • x) = f (g⁻¹ • x)
    rw [_root_.mul_inv_rev, mul_smul, triv N0 hN0n hN0H k⁻¹ (N0.inv_mem hk)]
  have hcont : ContAction ρ := by
    show Continuous fun p : Γ × M => ρ p.1 p.2
    rw [continuous_discrete_rng]
    intro b
    rw [isOpen_iff_forall_mem_open]
    rintro ⟨g, f⟩ hg
    refine ⟨((fun k => g⁻¹ * k) ⁻¹' (N0 : Set Γ)) ×ˢ {f}, ?_, ?_, ?_⟩
    · rintro ⟨k, f'⟩ ⟨hk, hf'⟩
      simp only [Set.mem_singleton_iff] at hf'
      subst hf'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
      rw [← hg]
      have e : k = g * (g⁻¹ * k) := by group
      rw [e, ρmul g _ hk]
    · exact (hN0o.preimage (continuous_const.mul continuous_id)).prod (isOpen_discrete _)
    · exact ⟨by show g⁻¹ * g ∈ (N0 : Set Γ); simp [N0.one_mem], rfl⟩
  let c : (H →* Multiplicative (ZMod n)) → Γ → M := fun φ g x =>
    Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩)
  have hcoc : ∀ φ : H →* Multiplicative (ZMod n), ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h) := by
    intro φ g h
    funext x
    show Multiplicative.toAdd (φ ⟨_, sec_mem H (g * h) x⟩) =
      Multiplicative.toAdd (φ ⟨_, sec_mem H g x⟩) + Multiplicative.toAdd (φ ⟨_, sec_mem H h (g⁻¹ • x)⟩)
    rw [← toAdd_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev, mul_smul]
    group
  have hZ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → c φ ∈ Z1 ρ := by
    intro φ hφ
    show Continuous (c φ) ∧ ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h)
    refine ⟨?_, hcoc φ⟩
    let K : Subgroup Γ := φ.ker.map H.subtype
    have hKo : IsOpen (K : Set Γ) := by
      simp only [K]
      rw [Subgroup.coe_map, Subgroup.coe_subtype]
      exact hH.isOpenMap_subtype_val _ hφ
    have hKH : (K : Set Γ) ⊆ H := by
      intro k hk
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hk
      exact y.2
    obtain ⟨N, hNn, hNo, hNK⟩ := getN (K : Set Γ) ⟨Subgroup.isClosed_of_isOpen K hKo, hKo⟩ K.one_mem
    have hk0 : ∀ k ∈ N, c φ k = 0 := by
      intro k hk
      funext x
      have hfix : k⁻¹ • x = x := triv N hNn (hNK.trans hKH) k⁻¹ (N.inv_mem hk) x
      have hmem : (x.out)⁻¹ * k * (k⁻¹ • x).out ∈ K := by
        rw [hfix]
        apply hNK
        have := hNn.conj_mem k hk (x.out)⁻¹
        simpa using this
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hmem
      show Multiplicative.toAdd (φ ⟨_, sec_mem H k x⟩) = 0
      have hyy : (⟨_, sec_mem H k x⟩ : H) = y := Subtype.ext hye.symm
      rw [hyy, MonoidHom.mem_ker.1 hy]
      rfl
    apply lc (c φ) N hNo
    intro g k hk
    rw [hcoc φ g k, hk0 k hk, map_zero, add_zero]
  let F : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → H1 ρ :=
    fun φ => Submodule.Quotient.mk ⟨c φ.1, hZ φ.1 φ.2⟩
  have hfin : Finite (H1 ρ) := h M ρ hcont
  refine Finite.of_injective F ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq
  have hq := (Submodule.Quotient.eq _).1 hEq
  rw [Submodule.mem_comap] at hq
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hq
  apply Subtype.ext
  apply MonoidHom.ext
  intro h
  let x0 : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hfix : (h : Γ)⁻¹ • x0 = x0 := by
    show (((h : Γ)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    apply QuotientGroup.eq.2
    simpa using h.2
  have ht : x0.out ∈ H := by
    have e : ((x0.out : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H) := QuotientGroup.out_eq' x0
    have := QuotientGroup.eq.1 e
    simpa using this
  have hval : ∀ χ : H →* Multiplicative (ZMod n), c χ h x0 = Multiplicative.toAdd (χ h) := by
    intro χ
    show Multiplicative.toAdd (χ ⟨_, sec_mem H h x0⟩) = _
    have hel : (⟨_, sec_mem H h x0⟩ : H) = (⟨x0.out, ht⟩ : H)⁻¹ * h * ⟨x0.out, ht⟩ := by
      apply Subtype.ext
      simp [hfix]
    rw [hel]
    congr 1
    rw [map_mul, map_mul, map_inv, mul_comm (χ ⟨x0.out, ht⟩)⁻¹ (χ h), mul_assoc, inv_mul_cancel, mul_one]
  have hx := congrFun (congrFun hm h) x0
  have hL : (d0 ρ m) h x0 = 0 := by
    show m ((h : Γ)⁻¹ • x0) - m x0 = 0
    rw [hfix, sub_self]
  have hR : (d0 ρ m) h x0 = c φ h x0 - c ψ h x0 := hx
  have hcc : c φ h x0 = c ψ h x0 := sub_eq_zero.1 (hR.symm.trans hL)
  rw [hval φ, hval ψ] at hcc
  exact hcc

theorem UpperTheory.galois_group_phi_condition :
    GlobalFiniteness → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))), ContainsAbove S l →
          PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) l ∧ CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) ∧ T2Space (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) ∧ TotallyDisconnectedSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := by
  intro hGF Ω _ _ _ l _ S hS
  haveI : IsClosed ((NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) : Set (G ℚ Ω))) := isClosed_NS Ω _
  refine ⟨?_, inferInstance, inferInstance, totDisc_quot _ (isClosed_NS Ω _)⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero 1 (Fact.out : l.Prime).ne_zero⟩
  have key := phi_condition_of_finite_cohomology (Γ := GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1)
    (fun M _ _ _ _ _ ρ hc => (hGF ℚ Ω l 1 M S ρ one_pos hS hc).2.1)
  rwa [pow_one] at key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.InertiaLeNormalIffKerLeAndInertiaLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem valuation_natCast_lt_one_iff_mem_asIdeal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (hA : IsPlaceOver A v) :
    A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hA ((l : ℕ) : 𝓞 ℚ)
  simpa using h

theorem UpperTheory.inertia_le_normal_iff_ker_le_and_inertia_le :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
          (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) → ∀ (H : Subgroup (G ℚ Ω)) [H.Normal], (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ H →
          ∀ (M : Subgroup (G ℚ Ω)) [M.Normal], IsClosed (M : Set (G ℚ Ω)) →
          ((∀ g, (∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A' ∧ g ∈ H) → g ∈ M) ↔
            ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ M ∧ ∀ v : S, v ≠ v₀ → Ine (F := ℚ) (A v) ⊓ H ≤ M)) := by
  intro Ω _ _ _ l _ S A v₀ hS hA hv₀ H _ hH M _ hM
  have hker : (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker = NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    simp [toGS, QuotientGroup.ker_mk']
  have hin : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 ℚ)), w ∉ (S : Set (HeightOneSpectrum (𝓞 ℚ))) →
      IsPlaceOver B w → (Ine (F := ℚ) B : Set (G ℚ Ω)) ⊆ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro B w hw hB g hg
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, B, hB, hg⟩
  constructor
  · intro h
    constructor
    · rw [hker]
      apply Subgroup.topologicalClosure_minimal _ _ hM
      apply Subgroup.normalClosure_le_normal
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨w, hw, B, hB, hgB⟩ := hg
      have hgI : g ∈ Ine (F := ℚ) B := hgB
      apply h g
      refine ⟨B, ?_, hgI, ?_⟩
      · rw [valuation_natCast_lt_one_iff_mem_asIdeal l B w hB]
        intro hl
        exact hw (by simpa using hS w hl)
      · apply hH
        rw [hker]
        exact hin B w hw hB hgI
    · intro v hv g hg
      rw [Subgroup.mem_inf] at hg
      apply h g
      refine ⟨A v, ?_, hg.1, hg.2⟩
      rw [valuation_natCast_lt_one_iff_mem_asIdeal l (A v) v.1 (hA v), hv₀]
      exact hv
  · rintro ⟨h1, h2⟩ g ⟨B, hBl, hgB, hgH⟩
    by_cases hBt : B = ⊤
    · subst hBt
      rw [(Kum.placeDict ℚ Ω).1] at hgB
      rw [Subgroup.mem_bot] at hgB
      subst hgB
      exact M.one_mem
    obtain ⟨w, hw⟩ := (Kum.placeDict ℚ Ω).2.1 B hBt
    by_cases hwS : w ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    · let u : S := ⟨w, hwS⟩
      have hu0 : u ≠ v₀ := by
        intro hu
        rw [← hv₀ u] at hu
        exact hBl ((valuation_natCast_lt_one_iff_mem_asIdeal l B w hw).2 hu)
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hA u) hw
      rw [← hσ] at hgB
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (A u) := ((ML.placeBasic Ω).2.2.2.2.2.2.2.2.2 (A u) σ).2.1 g |>.1 hgB
      have hcH : σ⁻¹ * g * σ ∈ H := by
        have := ‹H.Normal›.conj_mem g hgH σ⁻¹
        simpa [mul_assoc] using this
      have hcM := h2 u hu0 (Subgroup.mem_inf.2 ⟨hc, hcH⟩)
      have := ‹M.Normal›.conj_mem _ hcM σ
      simpa [mul_assoc] using this
    · apply h1
      rw [hker]
      exact hin B w hwS hw hgB
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem ipo_mul {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  rcases eq_or_ne (f z) 0 with h0 | h0
  · simp [h0]
  have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr h0
  suffices hx : ‖f x‖ ≤ 1 by nlinarith [norm_nonneg (f x)]
  by_contra hx
  push_neg at hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) hx
  have hmem : x ^ n * z ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hz
  have h1 := hf _ hmem
  rw [map_mul, map_pow, norm_mul, norm_pow] at h1
  have := (inv_lt_iff_one_lt_mul₀ hpos).mp hn
  linarith [mul_comm (‖f x‖ ^ n) ‖f z‖]

private theorem ipo_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  refine ⟨((s.sup fun g => ‖f g‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
  · have : (s.sup fun g => ‖f g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hgm : g ∈ maximalIdeal R := hs ▸ Ideal.subset_span hg
      have := hf g hgm
      exact_mod_cast this
    exact_mod_cast this
  · intro z hz
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      have : ‖f x‖₊ ≤ s.sup fun g => ‖f g‖₊ := Finset.le_sup (f := fun g => ‖f g‖₊) hx
      exact_mod_cast this
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihx ihy)
    | smul a x hx ihx =>
      rw [smul_eq_mul]
      refine (ipo_mul hf a ?_).trans ihx
      exact hs ▸ hx

private theorem ipo_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := ipo_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [zero_add, pow_one] at hz ⊢
      exact hρ z hz
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (hρ b hb) (norm_nonneg _) (pow_nonneg hρ0 _)
      · intro x y hx hy
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine ⟨n + 1, fun z hz => (key n z hz).trans_lt ?_⟩
  calc ρ ^ (n + 1) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ n)
    _ < ε := hn

private theorem ipo_cont {f : R →ₐ[O] K} (hf : IsLocPt f) {X : Type} [TopologicalSpace X] (u : X → R)
    (hu : AdicCont (maximalIdeal R) u) : Continuous fun g => f (u g) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := ipo_pow hf hε
  have hopen := (hu n).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal R ^ n) (u g))
  filter_upwards [hopen.mem_nhds rfl] with g' hg'
  have heq : Ideal.Quotient.mk (maximalIdeal R ^ n) (u g') = Ideal.Quotient.mk (maximalIdeal R ^ n) (u g) := hg'
  rw [Ideal.Quotient.eq] at heq
  rw [dist_eq_norm, ← map_sub]
  exact hn _ heq

end SlopeTestRemainingChoices

private theorem ipo_le_one {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  haveI := c.dvr
  haveI : IsLocalHom (algebraMap c.O R) := IsCO.isLocalHom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hm : algebraMap c.O R ϖ ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap c.O R) ϖ).mp hu)
  have hne : f (algebraMap c.O R ϖ) ≠ 0 := by
    rw [AlgHom.commutes]
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext (by simpa using h)
  have hpos : 0 < ‖f (algebraMap c.O R ϖ)‖ := norm_pos_iff.mpr hne
  have h := ipo_mul hf x hm
  rw [map_mul, norm_mul] at h
  nlinarith [norm_nonneg (f x)]

private theorem diagonal_rep_map_entries {G A B : Type} [Group G] [CommRing A] [CommRing B] (φ : A →+* B) (η : G →* ℤˣ) (Ψ : G →* Aˣ)
    (g : G) (a b : Fin 3) :
    (r0 η ((Units.map φ.toMonoidHom).comp Ψ) g).mat a b = φ ((r0 η Ψ g).mat a b) := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply, MonoidHom.comp_apply]
  split_ifs
  · first
      | (rw [← map_zpow, Units.coe_map]; rfl)
      | (rw [← map_pow, Units.coe_map]; rfl)
  · simp

theorem UpperTheory.V.U3.isPt_push :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁),
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f → D.IsPt U g₁ (push f S.r.hom) := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ _ S f hf
  have hid : S.r.map (AlgHom.id c.O S.R) = S.r := GLift.ext rfl
  have h0 := (S.rep S.R).1 (AlgHom.id c.O S.R)
  rw [hid] at h0
  obtain ⟨hn, hk, φ, hφ, hI⟩ := h0
  have hm : ∀ g a b, (push f S.r.hom g).mat a b = f ((S.r.hom g).mat a b) := fun _ _ _ => rfl
  refine ⟨fun g => S.r.hasMult g, ?_, fun g a b => ipo_le_one hf _, fun g a b => ?_, ⟨?_, ?_, ?_⟩, fun g hg => ?_,
    f.comp φ, fun x hx => hf _ ?_, fun x hx => ?_, ?_⟩
  · exact continuous_matrix fun a b => ipo_cont hf _ (S.r.cont a b)
  · have h1 : (r0 D.η D.ΨQ g).mat a b = algebraMap c.O (PadicAlgCl l) ((r0 D.η D.Ψ g).mat a b) :=
      diagonal_rep_map_entries _ _ _ _ _ _
    rw [hm, h1, ← f.commutes, ← map_sub]
    refine hf _ ((res_eq_zero_iff c.O S.R _).1 ?_)
    have h2 : res c.O S.R ((S.r.hom g).mat a b) = (rbar c.O D.η D.Ψ g).mat a b :=
      congrArg (fun x : GG 3 (ResidueField c.O) => x.mat a b) (S.r.red g)
    have h3 : (rbar c.O D.η D.Ψ g).mat a b = residue c.O ((r0 D.η D.Ψ g).mat a b) := diagonal_rep_map_entries _ _ _ _ _ _
    rw [map_sub, AlgHom.commutes, h2, h3]
    exact sub_self _
  · show (S.r.hom D.cc).mat.map (f : S.R →+* PadicAlgCl l) = 1
    rw [hn.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  · have := congrArg f hn.z12
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · have := congrArg f hn.z21
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · show GG.map (f : S.R →+* PadicAlgCl l) (S.r.hom g) = 1
    rw [hk g hg, map_one]
  · show φ x ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff c.O, res_map, res_eq_zero_iff]
    exact hx
  · have : φ x = 0 := hI hx
    show f (φ x) = 0
    rw [this, map_zero]
  · have h1 : (U.r.map φ).hom = S.r.hom.comp D.ι := congrArg GLift.hom hφ
    refine MonoidHom.ext fun g => ?_
    show GG.map (f : S.R →+* PadicAlgCl l) ((U.r.map φ).hom g) = _
    rw [h1]
    rfl
end

