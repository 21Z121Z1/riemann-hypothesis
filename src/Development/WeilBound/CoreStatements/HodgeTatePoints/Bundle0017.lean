import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Mathlib
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GeneratesDiffMap
section
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  {D : HTChart A K c p R N Ω}
  {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
  {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
  {φ : A →+* O} {P : HTPoint C O c κ' N V Ω'} {ι : D.om →ₛₗ[φ] Ω'}

theorem om'_le_om (D : HTChart A K c p R N Ω) : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem_om' (D : HTChart A K c p R N Ω) {x : Ω} (hx : x ∈ D.om) :
    (p : A) ^ R • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem span_om' (hred : D.ReducesTo φ P ι) (hκ : κ' ∣ (p : O) ^ R) :
    Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) = P.om' := by
  have hn : ∀ y : Ω', (p ^ R) • y = (p : O) ^ R • y := fun y => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hι : ∀ x : D.om, ι ((p : A) ^ R • x) = (p : O) ^ R • ι x := fun x => by
    rw [ι.map_smulₛₗ, map_pow, map_natCast]
  have a1 : ∀ y ∈ P.om, (p : O) ^ R • y ∈ P.om' := by
    intro y hy
    obtain ⟨w, hw⟩ := hκ
    obtain ⟨x, hx, e⟩ := P.κ_mem _ (P.om.smul_mem w hy)
    exact ⟨x, hx, by rw [hw, mul_smul]; exact e⟩
  have a2 : ∀ y ∈ P.om, (p : O) ^ R • y ∈
      Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
    intro y hy
    rw [← hred.span_eq] at hy
    have : Submodule.span O (Set.range ι) ≤ (Submodule.span O
        (ι '' {x : D.om | (x : Ω) ∈ D.om'})).comap ((p : O) ^ R • LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨(p : A) ^ R • x, pow_smul_mem_om' D x.2, hι x⟩
    exact this hy
  have ht : ∀ x, P.tate x ∈ P.T := by
    intro x
    refine P.T.sum_mem fun i _ => ?_
    rw [← (RingOfIntegers.basis E).sum_repr (x i), map_sum, LinearMap.sum_apply]
    refine P.T.sum_mem fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    refine zsmul_mem ?_ _
    rw [P.free.2.2]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  apply le_antisymm
  · have h : D.om' ≤ (P.om'.comap ι).map D.om.subtype := by
      refine sup_le (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨x, rfl⟩
        refine ⟨⟨D.h x, D.h_mem x⟩, ?_, rfl⟩
        obtain ⟨y, hy, e⟩ := hred.ht_eq x
        change ι _ ∈ P.om'
        rw [e, hn]
        exact P.om'.add_mem ⟨_, ht x, rfl⟩ (a1 y hy)
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨(p : A) ^ R • ⟨x, hx⟩, ?_, rfl⟩
        change ι _ ∈ P.om'
        rw [hι]
        refine a1 _ ?_
        rw [← hred.span_eq]
        exact Submodule.subset_span ⟨_, rfl⟩
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', e⟩ := h hx
    rw [← (Subtype.ext e : x' = x)]
    exact hx'
  · rw [HTPoint.om', Submodule.map_le_iff_le_comap]
    conv_lhs => rw [P.free.2.2]
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    have e0 : P.ρ (RingOfIntegers.basis E k) (P.t i) =
        P.tate (Pi.single i (RingOfIntegers.basis E k)) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    obtain ⟨y, hy, e⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ Submodule.span O _
    rw [e0, eq_sub_of_add_eq e.symm, hn]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, Submodule.mem_sup_left
      (Submodule.subset_span ⟨_, rfl⟩), rfl⟩) (a2 y hy)

omit [NumberField E] in
theorem transfer_mul [NumberField E] (hAK : Function.Injective (algebraMap A K)) {σ : E →+* K}
    {σ' : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (hφ : ∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E))
    {d a' : A} {e : E} (h : algebraMap A K a' = algebraMap A K d * σ e) :
    algebraMap O C (φ a') = algebraMap O C (φ d) * σ' e := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hb0 : algebraMap (𝓞 E) E b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨α, hα⟩ := hσ a
  obtain ⟨β, hβ⟩ := hσ b
  have h1 : a' * β = d * α := hAK (by
    rw [map_mul, map_mul, h, hα, hβ, map_div₀, mul_assoc,
      div_mul_cancel₀ _ ((map_ne_zero σ).2 hb0)])
  have h2 := congrArg (fun t => algebraMap O C (φ t)) h1
  simp only [map_mul, hφ a α hα, hφ b β hβ] at h2
  rw [map_div₀, ← mul_div_assoc, eq_div_iff ((map_ne_zero σ').2 hb0)]
  exact h2

theorem generatesDiff_map (hAK : Function.Injective (algebraMap A K)) {σ : E →+* K}
    {σ' : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (hφ : ∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E))
    {d : A} (hd : GeneratesDiff σ d) : GeneratesDiff σ' (φ d) := by
  apply le_antisymm
  · have key : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        ∃ a', algebraMap A K a' = y ∧ algebraMap O C (φ a') ∈
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ' (x : E)} := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨x, hx, rfl⟩ := h
        obtain ⟨a', ha'⟩ := hσ x
        exact ⟨a', ha', Submodule.subset_span ⟨x, hx, hφ x a' ha'⟩⟩
      | zero => exact ⟨0, map_zero _, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, ha'⟩ := hy
        obtain ⟨b, hb, hb'⟩ := hz
        exact ⟨a + b, by rw [map_add, ha, hb], by
          rw [map_add, map_add]; exact Submodule.add_mem _ ha' hb'⟩
      | smul r y _ hy =>
        obtain ⟨a, ha, ha'⟩ := hy
        exact ⟨r * a, by rw [map_mul, ha, Algebra.smul_def], by
          rw [map_mul, map_mul, ← Algebra.smul_def]; exact Submodule.smul_mem _ _ ha'⟩
    obtain ⟨a', ha, ha'⟩ := key _ (hd.le (Submodule.mem_span_singleton_self _))
    rw [hAK ha] at ha'
    exact (Submodule.span_singleton_le_iff_mem _ _).2 ha'
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hd.ge (Submodule.subset_span ⟨x, hx, rfl⟩))
    refine Submodule.mem_span_singleton.2 ⟨φ a, ?_⟩
    rw [← hφ x (a * d) (by rw [map_mul, ← ha, Algebra.smul_def]), map_mul, map_mul,
      Algebra.smul_def]

theorem smul_eigProj_eq (ρ : 𝓞 E →+* Module.End K Ω) {σ : E →+* K} {d : A}
    {cc : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A}
    (h : ∀ k, algebraMap A K (cc k) = algebraMap A K d * σ (dualInt E k)) (x : Ω) :
    d • eigProj ρ σ x = ∑ k, cc k • ρ (RingOfIntegers.basis E k) x := by
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul K (cc k), h, mul_smul, algebraMap_smul]

theorem span_eigQuot {σ : E →+* K} {σ' : E →+* C} {d : A}
    (h1 : ∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om)
    (h2 : ∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x → ι y = φ d • eigProj P.ρΩ σ' (ι x))
    {X : Submodule A Ω} (hX : X ≤ D.om) {X' : Submodule O Ω'}
    (hs : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ X}) = X') :
    Submodule.span O (ι '' {y : D.om | ∃ z ∈ eigQuot D.ρΩ σ X, (y : Ω) = d • z}) =
      (eigQuot P.ρΩ σ' X').map (φ d • LinearMap.id) := by
  rw [eigQuot, eigQuot, ← Submodule.map_comp, ← hs, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨y, ⟨_, ⟨x, hx, rfl⟩, e⟩, rfl⟩
    exact ⟨_, ⟨⟨x, hX hx⟩, hx, rfl⟩, (h2 ⟨x, hX hx⟩ y e).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨_, h1 x x.2⟩, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, h2 x _ rfl⟩

end

theorem red_proj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → GeneratesDiff σ' (φ d) ∧ (∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om) ∧ (∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x → ι y = φ d • eigProj P.ρΩ σ' (ι x)) ∧ Submodule.span O (ι '' {y : D.om | ∃ z ∈ D.omHT σ, (y : Ω) = d • z}) = (P.omHT σ').map (φ d • LinearMap.id) ∧ Submodule.span O (ι '' {y : D.om | ∃ z ∈ eigQuot D.ρΩ σ D.om, (y : Ω) = d • z}) = (P.omRec σ').map (φ d • LinearMap.id) := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D C _ _ _ v O _ _ hv κ' V _ _ _ _ Ω' _ _ _ _
    φ P ι hred σ σ' d hσ hφ hd hκ
  obtain ⟨-, hcc, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose cc hcc using hcc
  have h1 : ∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om := by
    intro x hx
    rw [smul_eigProj_eq _ hcc]
    exact D.om.sum_mem fun k _ => D.om.smul_mem _ (D.om_stable _ x hx)
  have h2 : ∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x →
      ι y = φ d • eigProj P.ρΩ σ' (ι x) := by
    intro x y e
    have hy : y = ∑ k, cc k • (⟨D.ρΩ (RingOfIntegers.basis E k) x, D.om_stable _ x x.2⟩ : D.om) := by
      apply Subtype.ext
      rw [e, smul_eigProj_eq _ hcc]
      simp
    rw [hy, map_sum, smul_eigProj_eq (cc := fun k => φ (cc k)) _
      (fun k => transfer_mul hAK hσ hφ (hcc k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ι.map_smulₛₗ, hred.lin]
  refine ⟨generatesDiff_map hAK hσ hφ hd, h1, h2,
    span_eigQuot h1 h2 (om'_le_om D) (span_om' hred hκ), span_eigQuot h1 h2 le_rfl ?_⟩
  rw [← hred.span_eq]
  congr 1
  ext w
  simp

end PositivityTheory.HtPt.Gb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.IsFractionRingOfIntegers
section
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped nonZeroDivisors

theorem isFractionRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsFractionRing O C := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 hv.hom_inj
  refine IsFractionRing.of_field O C fun z => ?_
  obtain ⟨a, h | h⟩ := hv.eq_algebraMap_or_inv_eq_algebraMap z
  · exact ⟨a, 1, by simp [h]⟩
  · exact ⟨1, a, by simp [← h]⟩

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (M : Submodule A Ω) (hM : M.IsLattice K) : finrank A M = finrank K Ω := by
  haveI : IsLocalizedModule A⁰ M.subtype :=
    { map_units := fun s => by
        rw [← (Algebra.lsmul A (A := K) A Ω).commutes]
        exact (IsLocalization.map_units K s).map _
      surj := fun y => by
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span A⁰ K (M : Set Ω) y
          (by rw [hM.span_eq_top]; trivial)
        rw [Submodule.span_eq] at ht
        exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.val_injective h]⟩ }
  rw [← IsLocalizedModule.finrank_eq A⁰ M.subtype le_rfl]
  exact (IsLocalization.finrank_eq K A⁰ le_rfl).symm

theorem rankAtStalk_eq_finrank {A : Type} [CommRing A] [IsDomain A] (M : Type) [AddCommGroup M]
    [Module A M] (p : PrimeSpectrum A) : rankAtStalk M p = finrank A M := by
  have hp : p.asIdeal.primeCompl ≤ A⁰ := p.asIdeal.primeCompl_le_nonZeroDivisors
  rw [rankAtStalk, IsLocalization.finrank_eq _ p.asIdeal.primeCompl hp,
    IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hp]

theorem finrank_baseChange_flat {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    [Algebra A O] (M : Type) [AddCommGroup M] [Module A M] [Module.Flat A M] [Module.Finite A M] :
    finrank O (O ⊗[A] M) = finrank A M := by
  rw [← rankAtStalk_eq_finrank (O ⊗[A] M) (⊥ : PrimeSpectrum O), rankAtStalk_baseChange,
    rankAtStalk_eq_finrank]

theorem exists_lift {A O : Type} [CommRing A] [CommRing O] [Algebra A O] {M : Type} [AddCommGroup M]
    [Module A M] {Ω' : Type} [AddCommGroup Ω'] [Module O Ω'] (ι : M →ₛₗ[algebraMap A O] Ω') :
    ∃ j : O ⊗[A] M →ₗ[O] Ω', (∀ x, j (1 ⊗ₜ x) = ι x) ∧
      LinearMap.range j = Submodule.span O (Set.range ι) := by
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι, map_smul' := fun a x => ι.map_smulₛₗ a x }
  refine ⟨f.liftBaseChange O, fun x => by simp [f], ?_⟩
  rw [LinearMap.range_liftBaseChange]
  rfl

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsLattice K → Module.Projective A M → L.IsLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hP hL hspan hrk
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := isFractionRing_of_integers hv
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  obtain ⟨j, hj, hr⟩ := exists_lift ι
  rw [hspan] at hr
  refine ⟨j, ?_, hr, hj⟩
  have h1 : finrank O (O ⊗[A] M) = finrank O (LinearMap.range j) := by
    rw [finrank_baseChange_flat, finrank_lattice M hM, hr, finrank_lattice L hL, hrk]
  have h2 := j.rank_range_add_rank_ker
  haveI : Module.Finite O (LinearMap.range j) := inferInstance
  rw [← finrank_eq_rank O (O ⊗[A] M), ← finrank_eq_rank O (LinearMap.range j), h1] at h2
  have h3 : Module.rank O (LinearMap.ker j) = 0 := by
    rw [add_comm] at h2
    exact (Cardinal.add_nat_inj _).1 (h2.trans (zero_add _).symm)
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.rank_eq_zero).1 h3

end PositivityTheory.HtPt.Gb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.LiftComul
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (spMap_comp spMap_id)

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

omit [GrpObj G] in
theorem spc {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap (ψ.comp φ) ≫ y = spMap ψ ≫ spMap φ ≫ y := by
  rw [← Category.assoc, spMap_comp]

omit [GrpObj G] in
theorem spc' {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap ψ ≫ spMap φ ≫ y = spMap (ψ.comp φ) ≫ y := (spc ψ φ y).symm

theorem tors_pow (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] (φ : T.A →ₐ[R] S) :
    (spMap φ ≫ T.y) ^ p = 1 := by
  rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]

theorem tors_ext (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] {φ φ' : T.A →ₐ[R] S}
    (h : spMap φ ≫ T.y = spMap φ' ≫ T.y) : φ = φ' := by
  exact (T.univ S _ (tors_pow T φ)).unique rfl h.symm

theorem lift_comul (T : TorsRep G p) (Δ : T.A →ₐ[R] TensorProduct R T.A T.A)
    (hΔ : spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y))
    {S : Type} [CommRing S] [Algebra R S] (F : TensorProduct R T.A T.A →ₐ[R] S) :
    spMap (F.comp Δ) ≫ T.y = (spMap (F.comp Algebra.TensorProduct.includeLeft) ≫ T.y) *
      (spMap (F.comp Algebra.TensorProduct.includeRight) ≫ T.y) := by
  rw [spc, hΔ, MonObj.comp_mul, spc', spc']

end

theorem tors_alg : ∀ (R : Type) [CommRing R] (p : ℕ), ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ T : TorsRep G p, ∃ (Δ : T.A →ₐ[R] TensorProduct R T.A T.A) (ε : T.A →ₐ[R] R) (s : T.A →ₐ[R] T.A), spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) ∧ spMap ε ≫ T.y = 1 ∧ (spMap s ≫ T.y) * T.y = 1 ∧ (Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp ((Algebra.TensorProduct.map Δ (AlgHom.id R T.A)).comp Δ) = (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp Δ ∧ (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp Δ = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp Δ = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp Δ = (Algebra.ofId R T.A).comp ε ∧ (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp Δ = Δ := by
  intro R _ p G _ _ T
  set iL : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeLeft with hiL
  set iR : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeRight with hiR
  have hz : ((spMap iL ≫ T.y) * (spMap iR ≫ T.y)) ^ p = 1 := by
    rw [mul_pow, tors_pow, tors_pow, _root_.one_mul]
  obtain ⟨Δ, hΔ, -⟩ := T.univ _ _ hz
  obtain ⟨ε, hε, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  have hz' : (T.y⁻¹) ^ p = 1 := by rw [inv_pow, T.y_p, inv_one]
  obtain ⟨s, hs, -⟩ := T.univ T.A _ hz'
  refine ⟨Δ, ε, s, hΔ, hε, by rw [hs, _root_.inv_mul_cancel], ?_, ?_, ?_, ?_, ?_⟩
  · apply tors_ext T
    rw [← AlgHom.comp_assoc, lift_comul T Δ hΔ, lift_comul T Δ hΔ]
    have e1 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iL = ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp Δ := by
      ext x; simp [hiL]
    have e2 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iR := by
      ext x; simp [hiR, Algebra.TensorProduct.one_def]
    have e3 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL]
    have e4 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp Δ := by
      ext x; simp [hiR]
    have e5 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL, Algebra.TensorProduct.one_def]
    have e6 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iL := by
      ext x; simp [hiL, hiR, Algebra.TensorProduct.one_def]
    rw [e1, e2, lift_comul T Δ hΔ, e5, e6, e3, e4, lift_comul T Δ hΔ, _root_.mul_assoc]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iL = (Algebra.TensorProduct.includeLeft : R →ₐ[R] TensorProduct R R T.A).comp ε := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iR = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.one_mul]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iL = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iR = (Algebra.TensorProduct.includeRight : R →ₐ[R] TensorProduct R T.A R).comp ε := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.mul_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iL = s := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iR = AlgHom.id R T.A := by
      ext x; simp [hiR]
    rw [e1, e2, spMap_id, Category.id_comp, hs, _root_.inv_mul_cancel, spc, hε, MonObj.comp_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ, hΔ]
    have e1 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iL = iR := by
      ext x; simp [hiL, hiR]
    have e2 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iR = iL := by
      ext x; simp [hiL, hiR]
    rw [e1, e2, _root_.mul_comm]

end PositivityTheory.HtPt.Rf
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LCentre.Centre

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have hab : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hab
    refine ⟨h0, a.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hab]
    exact b.2
  · rintro ⟨h0, -, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨(a : Ω)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem exists_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' hp'
  obtain ⟨c, hc, hreg⟩ := hp'
  haveI : IsLocalRing (regAt ξ' p') := (PositivityTheory.HtPt.Ma.reg_local X' Ω' ξ').1 p'
  let φ : chRing o x c →+* regAt ξ' p' :=
    (i.comp (chRing o x c).val.toRingHom).codRestrict (regAt ξ' p') (fun a => hreg a a.2)
  let P : Ideal (chRing o x c) := (IsLocalRing.maximalIdeal (regAt ξ' p')).comap φ
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p₀, ⟨hin, hP⟩, -⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω κ x M c hc P hPp
  have key : ∀ u : chRing o x c, unitAt M.ξ p₀ (u : Ω) ↔ unitAt ξ' p' (i u) := by
    intro u
    have h := hP u
    have h2 : u ∈ P ↔ ¬ unitAt ξ' p' (i u) := by
      change φ u ∈ IsLocalRing.maximalIdeal (regAt ξ' p') ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
      rfl
    tauto
  have hloc := fun (c₁ : κ) (p : Cpt M.ξ) (h : InChart M.ξ x c₁ p) =>
    PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ p h
  have hch : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := (hloc c p₀ hin).1
  have hdom : ∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have h1 := (key ⟨v, hv⟩).1 hvu
    rw [map_div₀, div_eq_mul_inv]
    exact mul_mem (hreg u hu) h1.2.2
  have hlift : ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a := by
    intro a ha hu'
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have hiu : unitAt ξ' p' (i u) := by
      have h1 : i u = i (u / v) * i v := by rw [← map_mul, div_mul_cancel₀ _ hvu.1]
      rw [h1]
      exact Flat.ZUnit.mul hu' ((key ⟨v, hv⟩).1 hvu)
    have hu0 : unitAt M.ξ p₀ u := (key ⟨u, hu⟩).2 hiu
    rw [div_eq_mul_inv]
    exact Flat.ZUnit.mul hu0 (Flat.ZUnit.inv hvu)
  have hchart : ∀ c₁, x c₁ ≠ 0 → (∀ j, i (x j / x c₁) ∈ regAt ξ' p') → InChart M.ξ x c₁ p₀ := by
    intro c₁ h1 hj
    have hmem : x c₁ / x c ∈ regAt M.ξ p₀ := hch _ (Algebra.subset_adjoin ⟨c₁, rfl⟩)
    have hunit : unitAt ξ' p' (i (x c₁ / x c)) := by
      refine ⟨(map_ne_zero i).2 (div_ne_zero h1 hc), hdom _ hmem, ?_⟩
      rw [← map_inv₀, inv_div]
      exact hj c
    have hu := hlift _ hmem hunit
    refine ⟨h1, fun j => ?_⟩
    have h2 : x j / x c₁ = x j / x c * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [h2]
    exact mul_mem (hch _ (Algebra.subset_adjoin ⟨j, rfl⟩)) hu.2.2
  refine ⟨p₀, ⟨hdom, hlift⟩, ?_, hchart⟩
  intro p hp
  rw [← PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p p₀]
  obtain ⟨c₁, hc₁⟩ := M.tie.cover p
  have hin₁ := hchart c₁ hc₁.1 (fun j => hp _ (hc₁.2 j))
  intro a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c₁ p hc₁).2 a).1 ha
  have hch₁ := (hloc c₁ p₀ hin₁).1
  have hv' : unitAt M.ξ p₀ v := hlift v (hch₁ v hv)
    ⟨(map_ne_zero i).2 hvu.1, hp v hvu.2.1, by rw [← map_inv₀]; exact hp _ hvu.2.2⟩
  rw [div_eq_mul_inv]
  exact mul_mem (hch₁ u hu) hv'.2.2

end PositivityTheory.HtPt.Mb.LCentre.Centre

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ :=
  @PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre
end

