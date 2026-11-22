import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CohomologyOfFiniteRepresentation
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FrameCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0027
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ShaInjGen

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Matrix IsLocalRing Module
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem res_surj {k G H M : Type} [CommRing k] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [AddCommGroup M] [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
    (ρ : Representation k G M) (e : H ≃* G) (he : Continuous e) (he' : Continuous e.symm) :
    Function.Surjective (resH2 ρ e.toMonoidHom he) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    refine ⟨Submodule.Quotient.mk ⟨fun p => c.1 (e.symm p.1, e.symm p.2), c.2.1.comp (he'.prodMap he'),
      fun g g' g'' => ?_⟩, congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))⟩
    · have := c.2.2 (e.symm g) (e.symm g') (e.symm g'')
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] at this
      simp only [map_mul]
      exact this
    · show c.1 (e.symm (e p.1), e.symm (e p.2)) = c.1 p
      rw [e.symm_apply_apply, e.symm_apply_apply]

private theorem contAction_of_open {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k G M)
    (h : IsOpen (ρ.ker : Set G)) : ContAction ρ := by
  refine continuous_prod_of_discrete_right.2 fun m => IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' ρ.ker, h.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have h1 : ρ (g⁻¹ * x) = 1 := hx
  show ρ x m = ρ g m
  rw [← mul_inv_cancel_left g x, map_mul, h1, mul_one]

private theorem contAction_comp {k G H M : Type} [CommRing k] [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] [AddCommGroup M] [Module k M] [TopologicalSpace M] (ρ : Representation k G M)
    (h : ContAction ρ) (φ : H →* G) (hφ : Continuous φ) : ContAction (ρ.comp φ : Representation k H M) :=
  Continuous.comp h (hφ.prodMap continuous_id)

private theorem arith {h0 h1c L1 Q1 h2 L0 h1 Q0 ob L2 Q2 d f : ℕ}
    (c3 : h0 + h1c + L1 + Q1 + h2 + 0 = L0 + h1 + Q0 + ob + L2 + Q2) (e1 : Q1 = Q0 + Q2) (e2 : L1 = L0 + L2 + d)
    (g3 : h0 + h2 + d = h1 + f) : ob = h1c + f := by omega

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.U3.box_count (hI : CohInp) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] (hl : l ≠ 2)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S) (hS : ContainsAbove S l)
    (hA : ∀ v, IsPlaceOver (A v) v.1) (hv : ∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀)
    (ι : GQ l →* G ℚ Ω) (hι : Continuous ι) (hinj : Function.Injective ι) (hr : ι.range = Dec (F := ℚ) (A v₀))
    (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M)
    (hρ : IsOpen (ρ.ker : Set (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))))))
    [Fintype {v : S // v ≠ v₀}] (N : {v : S // v ≠ v₀} → Subgroup (G ℚ Ω)) (hN1 : ∀ q, N q ≤ Ine (F := ℚ) (A q))
    (hN2 : ∀ q, ((N q).subgroupOf (Dec (F := ℚ) (A q))).Normal) (hN3 : ∀ q, IsClosed (N q : Set (G ℚ Ω)))
    (hN4 : ∀ q, ∀ n ∈ N q, ρ (toGS Ω _ n) = 1) (hN5 : ∀ q, ¬ l ∣ (N q).relIndex (Ine (F := ℚ) (A q)))
    (hg : ∃ g : G ℚ Ω, cycMod ℚ Ω l 1 g = -1 ∧ ρ (toGS Ω _ g) = 1)
    (σ : G ℚ Ω) (hσ : ∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x)) :
    Module.Finite k ((unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N).Ob ρ) ∧
      finrank k ((unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N).Ob ρ) =
        finrank k ((unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N).H1c ρ) +
          finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : IsTopologicalAddGroup M :=
    { continuous_add := continuous_of_discreteTopology, continuous_neg := continuous_of_discreteTopology }
  haveI : ContinuousConstSMul k M := ⟨fun _ => continuous_of_discreteTopology⟩
  letI : Algebra ℤ_[l] k := ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod).toAlgebra
  have hπ := continuous_toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))
  have hc := contAction_of_open ρ hρ
  set F := unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N with hF
  obtain ⟨g1, g2, g3⟩ := UpperTheory.global_euler_char_rat_of_ne_two hI.gf hI.ge Ω l k M hl S hS ρ hc σ hσ
  obtain ⟨l1, l2, l3, -⟩ := Loc.tateFin hI.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id k M
    (ρ.comp ((toGS Ω _).comp ι)) (contAction_comp ρ hc _ (hπ.comp hι))
  rw [if_pos rfl, MonoidHom.range_eq_top.2 Function.surjective_id, Subgroup.index_top, one_mul] at l3
  have hq : ∀ q : {v : S // v ≠ v₀}, _ := fun q => UpperTheory.local_euler_characteristic_of_prime_not_mem hI.loc.lf hI.loc.le Ω l k M (A q) q.1.1 (hA q)
    (fun h => q.2 ((hv q).1 h)) (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A q)).subtype))
    (contAction_comp ρ hc _ (hπ.comp continuous_subtype_val))
  have hur : ∀ q : {v : S // v ≠ v₀}, finrank k (H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) =
      finrank k (H0 (ρ.comp (F.ψ q) : Representation k _ M)) := fun q => by
    obtain ⟨d1, d2, d3, d4, d5⟩ := UpperTheory.exists_decompositionField_frobenius_data Ω (A q) q.1.1 (hA q)
    haveI := hN2 q
    refine UpperTheory.cohomology_of_finite_representation l k M (Dec (F := ℚ) (A q)) (ρ.comp (F.ψ q)) (hρ.preimage (F.hψ q)) _ _ (d3.preimage continuous_subtype_val)
      ((hN3 q).preimage continuous_subtype_val) (fun x hx => hN1 q hx) (fun x hx => hN4 q x hx) ?_ d4
      fun n => d5 _ (pow_pos (Fact.out : l.Prime).pos n)
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _)]
    exact hN5 q
  have hsurj : LinearMap.range ((LinearMap.pi fun v => resH2 ρ (F.φ v) (F.hφ v)).prod
      (LinearMap.pi fun q => resH2 ρ (F.ψ q) (F.hψ q))) = ⊤ := by
    classical
    rw [eq_top_iff]
    rintro ⟨x, y⟩ -
    let e : GQ l ≃* Dec (F := ℚ) (A v₀) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
    have he : Continuous e := hι.subtype_mk _
    have he' : Continuous e.symm := (he.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous
    obtain ⟨x', hx'⟩ := res_surj (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v₀)).subtype)) e he he' (x ())
    obtain ⟨z, hz⟩ := UpperTheory.global_euler_characteristic_odd hI.pt Ω l k M hl S A hS hA ρ hc hg
      fun v => if h : v = v₀ then h ▸ x' else y ⟨v, h⟩
    refine ⟨z, Prod.ext (funext fun _ => ?_) (funext fun q => ?_)⟩
    · have h0 := hz v₀
      rw [dif_pos rfl] at h0
      have h1 : _ = x' := h0
      refine Eq.trans ?_ hx'
      rw [← h1]
      induction z using Submodule.Quotient.induction_on with
      | H c => rfl
    · have h0 := hz q.1
      rw [dif_neg q.2] at h0
      exact h0
  obtain ⟨-, c2, c3⟩ := frame_count k _ M ρ hρ F (fun q n hn => hN4 q n hn) g1 g2 (fun _ => ⟨l1, l2⟩)
    fun q => ⟨(hq q).1, (hq q).2.1⟩
  refine ⟨c2, ?_⟩
  rw [@finrank_zero_of_subsingleton k _ _ _ _ _ (Submodule.Quotient.subsingleton_iff.2 hsurj), Finset.sum_congr rfl fun q _ => hur q] at c3
  have e1 : ∑ q, finrank k (H1 (ρ.comp (F.ψ q) : Representation k _ M)) =
      ∑ q, finrank k (H0 (ρ.comp (F.ψ q) : Representation k _ M)) +
        ∑ q, finrank k (H2 (ρ.comp (F.ψ q) : Representation k _ M)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => (hq q).2.2
  have e2 : ∑ v, finrank k (H1 (ρ.comp (F.φ v) : Representation k _ M)) =
      ∑ v, finrank k (H0 (ρ.comp (F.φ v) : Representation k _ M)) +
        ∑ v, finrank k (H2 (ρ.comp (F.φ v) : Representation k _ M)) + finrank k M := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact l3
  exact arith c3 e1 e2 g3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem dx_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] :
    ∃ σ : G ℚ Ω, ∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x) := by
  obtain ⟨σ, h⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [eq_ratCast (algebraMap ℚ Ω), map_ratCast], h⟩

private theorem dx_ker (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (σ : G ℚ Ω) : AlgEquiv.restrictNormalHom (F := ℚ) K σ = 1 ↔ σ ∈ galOf ℚ K Ω := by
  have h : ∀ x : K, algebraMap K Ω (AlgEquiv.restrictNormalHom (F := ℚ) K σ x) = σ (algebraMap K Ω x) :=
    fun x => AlgEquiv.restrictNormal_commutes σ K x
  refine ⟨fun h1 x => ?_, fun h1 => AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_⟩
  · rw [← h, h1]; rfl
  · rw [h, h1]; rfl

private theorem dx_eta (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (h2 : Module.finrank ℚ K = 2) : ∃ η : G ℚ Ω →* ℤˣ, η.ker = galOf ℚ K Ω := by
  have hc : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hz : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  let e : Gal(K/ℚ) ≃* ℤˣ := mulEquivOfPrimeCardEq hc hz
  refine ⟨e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) K), Subgroup.ext fun σ => ?_⟩
  rw [← dx_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact map_eq_one_iff e e.injective

private theorem dx_unr (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsGalois ℚ K] (l : ℕ) [hl : Fact l.Prime] (h : ¬ (l : ℤ) ∣ discr K) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨p1, p2, p3, -⟩ := places K Ω l A
  obtain ⟨w, hw⟩ := p1 fun ht => (p2 ht).2 hA
  have hm : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := (p3 w hw).1 hA
  have hb := (CF.unramIff.1 K l hl.out).1 ((CF.unramIff.2.1 K l hl.out).2 h) w hm
  intro σ hσ
  have h1 := Subgroup.mem_map_of_mem (CF.resTo ℚ K Ω) hσ
  rw [CF.ineAbs ℚ K Ω A w hw, hb, Subgroup.mem_bot] at h1
  exact (dx_ker Ω K σ).1 h1

private theorem dx_lc {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group M] (f : Γ →* M)
    (h : IsOpen (f.ker : Set Γ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Γ => x⁻¹ * y := by fun_prop
  have h1 : (fun y : Γ => x⁻¹ * y) ⁻¹' (f.ker : Set Γ) ∈ nhds x :=
    (h.preimage hc).mem_nhds (by simp)
  filter_upwards [h1] with y hy
  have h2 : f (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem dx_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  classical
  intro N
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((Ψ g ^ j : Rˣ) : R)) =
      (fun x : R ⧸ I ^ N => if hx : IsUnit x then ((hx.unit ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N) else 0) ∘
        fun g => Ideal.Quotient.mk (I ^ N) (Ψ g : R) := by
    funext g
    have hx : IsUnit (Ideal.Quotient.mk (I ^ N) (Ψ g : R)) := (Ψ g).isUnit.map _
    have e : hx.unit = Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (Ψ g) := Units.ext rfl
    simp only [Function.comp_apply, dif_pos hx]
    rw [e, ← map_zpow]
    rfl
  rw [key]
  exact (h N).comp _

private theorem dx_alg {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R]
    (I : Ideal R) (hI : (l : R) ∈ I) (f : Γ → ℤ_[l]) (hf : Continuous f) :
    AdicCont I fun g => algebraMap ℤ_[l] R (f g) := by
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hf.continuousAt.eventually (Metric.closedBall_mem_nhds (f x) hpos)] with y hy
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, ha⟩ := hy
  rw [Ideal.Quotient.eq, ← map_sub, ← ha, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hI n)

private theorem dx_lmem (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) = IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have h1 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h, Ideal.mem_comap, map_natCast] at h1
  exact h1

private theorem dx_dir (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) : IsLocallyConstant (Chr.dirG ℚ Ω ψ) :=
  (dx_lc _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom

private theorem dx_cont (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) : CharCont (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) := by
  refine dx_zpow _ _ fun n => ?_
  have h1 : AdicCont (IsLocalRing.maximalIdeal O) fun g => (chiO ℚ Ω l O g : O) :=
    dx_alg _ (dx_lmem l O) (fun g => (cycZ ℚ Ω l g : ℤ_[l])) (Units.continuous_val.comp (contTw ℚ Ω l).1)
  have h2 := dx_zpow _ _ h1 (e : ℤ) n
  have h3 := (dx_dir Ω ψ).comp fun u : Oˣ => Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n) (u : O)
  have h4 := h2.mul h3
  convert h4 using 1
  funext g
  simp only [Chr.Psi, MonoidHom.mul_apply, Units.val_mul, map_mul, Pi.mul_apply, Function.comp_apply]
  rfl

private theorem dx_place {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [hl : Fact l.Prime] (j : Ω →+* Om l) :
    (Loc.placeJ j).valuation (l : Ω) < 1 := by
  have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have h1 : (l : Ω)⁻¹ ∉ Loc.placeJ j := by
    intro h
    have h2 : ‖j (l : Ω)⁻¹‖ ≤ 1 := h
    have h3 : j (l : Ω)⁻¹ = algebraMap ℚ_[l] (Om l) (l : ℚ_[l])⁻¹ := by simp
    rw [h3, PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv] at h2
    exact absurd hl.out.one_lt (by exact_mod_cast h2.not_gt)
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).2 h0)] at h1
  exact h1

theorem UpperTheory.V.U3.exists_dat :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}, GD Ω K l e ψ → Nonempty (Dat Ω K c e ψ) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h.quad⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨η, hη⟩ := dx_eta Ω K h.quad
  obtain ⟨cc, hcc⟩ := dx_cc Ω
  obtain ⟨j⟩ := Loc.exists_emb (Ω := Ω) (v := l)
  obtain ⟨i1, -, i3, -, i5, -⟩ := Loc.iotaFacts j
  have hA : (Loc.placeJ j).valuation (l : Ω) < 1 := dx_place j
  have hI : ∀ g ∈ Loc.Iq l, Loc.iota j g ∈ Ine (F := ℚ) (Loc.placeJ j) := fun g hg => by
    rw [← i3] at hg; exact hg
  have hopen : IsOpen (((η.comp (Loc.iota j)).ker : Subgroup (GQ l)) : Set (GQ l)) := by
    have h1 := (galEmbTop ℚ K Ω).2.1
    rw [← hη] at h1
    exact h1.preimage i1.continuous
  obtain ⟨Kv, -, -, -, -, hKv, -⟩ := Loc.openField (η.comp (Loc.iota j)).ker.subtype hopen.isOpenEmbedding_subtypeVal
  rw [Subgroup.range_subtype] at hKv
  have hd : ¬ (l : ℤ) ∣ discr K := fun hd => h.l_cop (Dvd.dvd.mul_right (Int.natCast_dvd.1 hd) _)
  exact ⟨{
    gd := h
    η := η
    η_ker := hη
    cc := cc
    conj := hcc
    j := j
    ι := Loc.iota j
    ι_cont := i1.continuous
    ι_spec := fun σ x => (Loc.iota_spec j σ x).symm
    Kv := Kv
    Kv_spec := fun g => by rw [← hKv]; rfl
    η_unr := fun g hg => by
      have h1 := dx_unr Ω K l hd _ hA (hI g hg)
      rw [← hη] at h1
      exact h1
    τ_open := ((dx_dir Ω (comp l ψ)).comp_continuous i1.continuous).isOpen_fiber 1
    Ψ_cont := dx_cont Ω e ψ
    Ψ_I := fun g hg => by
      rw [← ((compIne Ω N l hl.out _ hA).2 c.O ψ).1 _ (hI g hg), Chr.Psi, MonoidHom.mul_apply, zpow_natCast,
        MonoidHom.pow_apply, Loc.cycA, ← i5 l]
      rfl }⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFinitePlaceSetFactoringThroughGS
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem place_uniq {l : ℕ} (hl : l.Prime) (v w : HeightOneSpectrum (𝓞 ℚ)) (hv : (l : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (l : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have key : ∀ u : HeightOneSpectrum (𝓞 ℚ), (l : 𝓞 ℚ) ∈ u.asIdeal →
      Ideal.span {(l : ℤ)} = u.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    intro u hu
    apply hmax.eq_of_le
    · rw [Ideal.map_comap_of_equiv]
      exact Ideal.comap_ne_top _ u.isPrime.ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hel : e (l : 𝓞 ℚ) = (l : ℤ) := map_natCast e l
      rw [← hel]
      exact Ideal.mem_map_of_mem _ hu
  apply HeightOneSpectrum.ext
  rw [← Ideal.map_of_equiv (I := v.asIdeal) e, ← Ideal.map_of_equiv (I := w.asIdeal) e, ← key v hv, ← key w hw]

theorem UpperTheory.exists_finite_place_set_factoring_through_GS :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S) (η' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* ℤˣ) (Ψ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* c.Oˣ),
            ContainsAbove S l ∧ (∀ v, IsPlaceOver (A v) v.1) ∧ D.ι.range = Dec (F := ℚ) (A v₀) ∧ (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) ∧
            η'.comp (toGS Ω _) = D.η ∧ Ψ'.comp (toGS Ω _) = D.Ψ := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  classical
  have hlp : l.Prime := Fact.out
  obtain ⟨-, -, -, hηlc, -, -, -, -, -, -, -⟩ := dat_facts D
  haveI : IsScalarTower ℚ K Ω := inferInstance
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨⟨T, hT⟩, -⟩ := ramFinite ℚ ℚ K Ω
  have hlN0 : ((l * N : ℕ) : 𝓞 ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hlp.ne_zero (NeZero.ne N))
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := T ∪ hfin.toFinset
  have hmemS : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply Finset.mem_union_right
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  have hcast : ∀ n : ℕ, algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := fun n => by simp
  have hlv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv
  have hNv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hv
  obtain ⟨A₀, hA₀l, hA₀dec, -⟩ := dat_loc D
  have hA₀top : A₀ ≠ ⊤ := by
    intro h
    exact ((places ℚ Ω l A₀).2.1 h).2 hA₀l
  obtain ⟨v₀, hv₀⟩ := (places ℚ Ω l A₀).1 hA₀top
  have hlv₀ : ((l : ℕ) : 𝓞 ℚ) ∈ v₀.asIdeal := by
    rw [← hv₀, hcast]
    exact hA₀l
  have hv₀S : v₀ ∈ S := hmemS v₀ (hlv v₀ hlv₀)
  let v₀' : S := ⟨v₀, hv₀S⟩
  let A : S → ValuationSubring Ω := fun v =>
    if v.1 = v₀ then A₀ else Classical.choose (exists_isPlaceOver Ω v.1)
  let H : Subgroup (G ℚ Ω) := (cycZ ℚ Ω l).ker ⊓ (Chr.cls ℚ Ω N).ker ⊓ D.η.ker
  have hHclosed : IsClosed (H : Set (G ℚ Ω)) := by
    simp only [H, Subgroup.coe_inf]
    refine (IsClosed.inter ?_ ?_).inter ?_
    · rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (contTw ℚ Ω l).1
    · exact Subgroup.isClosed_of_isOpen _ (Chr.clsFacts ℚ Ω N).1
    · exact Subgroup.isClosed_of_isOpen _ (hηlc.isOpen_fiber 1)
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ H := by
    apply Subgroup.topologicalClosure_minimal _ _ hHclosed
    apply Subgroup.normalClosure_le_normal
    simp only [Set.iUnion_subset_iff]
    intro v hv B hB g hg
    have hg' : g ∈ Ine (F := ℚ) B := hg
    have hvS : v ∉ S := hv
    have hvT : v ∉ T := fun h => hvS (Finset.mem_union_left _ h)
    have hlB : ¬ B.valuation (l : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hlv v ((hB _).mp h)))
    have hNB : ¬ B.valuation (N : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hNv v ((hB _).mp h)))
    refine ⟨⟨(places ℚ Ω l B).2.2.2 hlB hg', (Chr.clsFacts ℚ Ω N).2.2.2.2 B hNB hg'⟩, ?_⟩
    show g ∈ D.η.ker
    rw [D.η_ker]
    exact hT v hvT B hB ⟨by rw [galOf_self]; trivial, hg'⟩
  have hηk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.η.ker := hNS.trans inf_le_right
  have hΨk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.Ψ.ker := by
    intro g hg
    have hH := hNS hg
    have h1 : cycZ ℚ Ω l g = 1 := hH.1.1
    have h2 : Chr.cls ℚ Ω N g = 1 := hH.1.2
    rw [MonoidHom.mem_ker]
    simp [Dat.Ψ, Chr.Psi, chiO, Chr.dirG, h1, h2]
  refine ⟨S, A, v₀', QuotientGroup.lift _ D.η hηk, QuotientGroup.lift _ D.Ψ hΨk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact hmemS v (hlv v hv)
  · intro v
    by_cases h : v.1 = v₀
    · simp only [A, if_pos h]
      rw [h]
      exact hv₀
    · simp only [A, if_neg h]
      exact Classical.choose_spec (exists_isPlaceOver Ω v.1)
  · simp only [A, v₀', if_pos rfl]
    exact hA₀dec
  · intro v
    constructor
    · intro hv
      exact Subtype.ext (place_uniq hlp _ _ hv hlv₀)
    · rintro rfl
      exact hlv₀
  · ext g
    rfl
  · ext g
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ShaInj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

abbrev UpperTheory.V.U3.CocVal {O : Type} [CommRing O] (a : O) : Type := Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})

private theorem shaInj_loc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    D.ι.range ∈ shaFam ℚ Ω (l * N) ∧ ∃ s', IsUnit ((D.Ψ (D.ι s') : c.O) ^ 2 - 1) := by
  obtain ⟨A, hA, hD, hIn, -⟩ := dat_loc D
  obtain ⟨s, hs, hsu⟩ := ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).2
  rw [← hIn] at hs
  obtain ⟨s', -, hs'⟩ := Subgroup.mem_map.1 hs
  refine ⟨?_, s', by rw [hs']; exact hsu⟩
  rw [hD]
  exact Chr.shaFam_mono (dvd_mul_right l N) (Or.inl ⟨A, hA, rfl⟩)

private theorem shaInj_away {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    ∀ g ∈ D.Kill, ∃ D' ∈ shaFam ℚ Ω (l * N), g ∈ D' := by
  rintro g ⟨A', -, hg', -⟩
  exact ⟨_, Or.inr ⟨A', rfl⟩, hg'⟩

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.U3.sha_inj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ → ∀ b : c.O, b ≠ 0 → ∃ a : c.O, a ≠ 0 ∧
      ∃ γ : Submodule.torsionBy c.O (ShaU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (l * N) ⊤) b →+ (G ℚ Ω → CocVal a),
        Function.Injective γ ∧ ∀ x, γ x ∈ shaCoc D.η D.Ψ D.Kill D.ι D.cc g₁ a := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ hM b hb
  exact ⟨b, hb, sha_inj_gen (O := c.O) e (l * N) (Chr.dirG ℚ Ω ψ) D.η D.Kill D.ι D.cc g₁ b hb hM
    (dat_facts D).2.2.2.2.2.2.1 (dat_facts D).2.2.2.2.2.1 (shaInj_away D) (shaInj_loc D).1 _
    (shaInj_loc D).2.choose_spec⟩
end

