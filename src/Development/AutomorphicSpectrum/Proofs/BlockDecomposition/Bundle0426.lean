import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.LatticeUnfoldingLerayVolume

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
section
noncomputable section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology

namespace GlobalTheory.CompanionTheory.CTFin.Central

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_mul {r : ℕ} {φ : Sm E a} (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set f₀ := JointCont.finPart g x₀
  have hc : Continuous (fun x : BlockIx a r → Ad E => f₀⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a (f₀⁻¹ * f₀) φ = φ := by rw [inv_mul_cancel]; simp
  have hev : ∀ᶠ x in 𝓝 x₀, chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val) = φ.1 (unip x * g) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.mem_nhds h1)] with x hx
    have hx' : finRep E a (f₀⁻¹ * JointCont.finPart g x) φ = φ := hx
    have e : unip x * g = finGL E a f₀ * infGL E a (JointCont.infPart g x) * finGL E a (f₀⁻¹ * JointCont.finPart g x) := by
      rw [JointCont.unip_mul_eq, mul_assoc, infGL_comm, ← mul_assoc, ← map_mul (finGL E a), mul_inv_cancel_left]
    rw [chart_val, e]
    exact (congrArg (fun ψ : Sm E a => ψ.1 (finGL E a f₀ * infGL E a (JointCont.infPart g x))) hx').symm
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E => chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a f₀))
      ((φ.2 _).continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  exact hA.congr hev

theorem exists_bound_unip_mul {r : ℕ} {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_unip_mul (r := r) hφ g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hper : φ.1 (unip x * g) = φ.1 (unip (fun p => x p - algebraMap E (Ad E) (q p)) * g) := by
    conv_lhs => rw [hx]
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hper]
  exact hC _ fun p _ => hq p

theorem integrable_unip_mul {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) (μ.restrict 𝓕) := by
  have hfin := covol_lt_top μ 𝓕 h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) hl hφ g
  exact Integrable.of_bound (continuous_unip_mul hφ g).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem ct_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 hlie
  haveI := hμ
  let P : Sm E a → Prop := fun φ =>
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}
  have hadd : ∀ φ ψ : Sm E a, P φ → P ψ → P (φ + ψ) := fun φ ψ h1 h2 =>
    ⟨fun γ g => by
      change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
      rw [h1.1, h2.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).add_mem (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)
       (show ψ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h2.2)⟩
  have hsmul : ∀ (c : ℂ) (φ : Sm E a), P φ → P (c • φ) := fun c φ h1 =>
    ⟨fun γ g => by
      change c • φ.1 _ = c • φ.1 _
      rw [h1.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).smul_mem c (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)⟩
  have hint : ∀ ψ : Sm E a, P ψ → ∀ g, Integrable (fun x => ψ.1 (unip x * g)) (μ.restrict 𝓕) :=
    fun ψ h g => integrable_unip_mul μ 𝓕 h𝓕 h.1 h.2 g
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {T | ∀ φ, P φ → P (T φ) ∧ ∀ F : Sm E a, (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
          ∀ g, (T F).1 g = ∫ x in 𝓕, (T φ).1 (unip x * g) ∂μ}
      mul_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₂ φ hφ
        obtain ⟨h2, e2⟩ := hT₁ _ h1
        exact ⟨h2, fun F hF g => e2 (T₂ F) (e1 F hF) g⟩
      add_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₁ φ hφ
        obtain ⟨h2, e2⟩ := hT₂ φ hφ
        refine ⟨hadd _ _ h1 h2, fun F hF g => ?_⟩
        change (T₁ F).1 g + (T₂ F).1 g = ∫ x in 𝓕, ((T₁ φ).1 (unip x * g) + (T₂ φ).1 (unip x * g)) ∂μ
        rw [integral_add (hint _ h1 g) (hint _ h2 g), e1 F hF g, e2 F hF g]
      algebraMap_mem' := fun c φ hφ => by
        refine ⟨by rw [Module.algebraMap_end_apply]; exact hsmul c φ hφ, fun F hF g => ?_⟩
        rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        change c • F.1 g = ∫ x in 𝓕, c • φ.1 (unip x * g) ∂μ
        rw [integral_smul, hF g] }
  have hL : ∀ X, lie E a X ∈ S := fun X φ hφ =>
    ⟨⟨fun γ g => GlobalTheory.SpehInfChar.lie_leftInv (ratGL E a).range X
        (fun u hu g' => by obtain ⟨γ', rfl⟩ := MonoidHom.mem_range.1 hu; exact hφ.1 γ' g') _ ⟨γ, rfl⟩ g,
      GlobalTheory.SpehInfChar.lie_mem_smoothPart X (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from hφ.2)⟩,
     fun F hF g => hlie φ F hφ.1 hφ.2 hF X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  intro φ F hl hlev hF z hz g
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, hlev⟩).2 F hF g

end GlobalTheory.CompanionTheory.CTFin.Central
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInvOfPowEqOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel Filter Topology PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc.KillNlo

section Generic

variable {G : Type} [Group G]

theorem exists_fixed_of_contract [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {K S : Set G} (hK : IsCompact K) (hSK : S ⊆ K) (h1 : (1 : G) ∈ S) {Ψ φ : G → G}
    (hΨ : Continuous Ψ) (hΨS : ∀ x ∈ S, Ψ x ∈ S) (hφS : ∀ x ∈ S, φ x ∈ S)
    (hid : ∀ x y, (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y)) {l : ℕ} (hl : 0 < l)
    (hc : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ S, φ^[l * m] x ∈ U) :
    ∃ v ∈ K, Ψ v = v :=
  _root_.UpperTheory.Reformulated.B.Ydb1.main hK hSK h1 hΨ hΨS hφS hid hl hc

theorem tnorm_zero (θ : MulAut G) (x : G) : tnorm θ 0 x = 1 := by
  simp [tnorm]

theorem tnorm_succ (θ : MulAut G) (i : ℕ) (x : G) :
    tnorm θ (i + 1) x = tnorm θ i x * (θ ^ i) x := by
  unfold tnorm
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  rfl

theorem pow_apply_mem {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) (i : ℕ) {x : G}
    (hx : x ∈ H) : (θ ^ i) x ∈ H := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply, ← h]
    exact Subgroup.mem_map_of_mem _ ih

theorem inv_apply_mem {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) {x : G}
    (hx : x ∈ H) : θ⁻¹ x ∈ H := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem tnorm_mem {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) (i : ℕ) {x : G}
    (hx : x ∈ H) : tnorm θ i x ∈ H := by
  induction i with
  | zero => rw [tnorm_zero]; exact H.one_mem
  | succ i ih => rw [tnorm_succ]; exact H.mul_mem ih (pow_apply_mem h i hx)

theorem tnorm_mul_of_comm {T : Subgroup G} {θ : MulAut G} (h : T.map θ.toMonoidHom = T)
    (hc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (i : ℕ) {x y : G} (hx : x ∈ T) (hy : y ∈ T) :
    tnorm θ i (x * y) = tnorm θ i x * tnorm θ i y := by
  induction i with
  | zero => simp [tnorm_zero]
  | succ i ih =>
    rw [tnorm_succ, tnorm_succ, tnorm_succ, ih, map_mul]
    have := hc _ (tnorm_mem h i hy) _ (pow_apply_mem h i hx)
    calc tnorm θ i x * tnorm θ i y * ((θ ^ i) x * (θ ^ i) y)
        = tnorm θ i x * (tnorm θ i y * (θ ^ i) x) * (θ ^ i) y := by simp only [mul_assoc]
      _ = tnorm θ i x * ((θ ^ i) x * tnorm θ i y) * (θ ^ i) y := by rw [this]
      _ = _ := by simp only [mul_assoc]

theorem iterate_twist (θ : MulAut G) (u : G) (i : ℕ) (x : G) :
    (fun y => θ⁻¹ (u⁻¹ * y * u))^[i] x =
      (θ⁻¹ ^ i) ((tnorm θ i u)⁻¹ * x * tnorm θ i u) := by
  induction i with
  | zero => simp [tnorm_zero]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, tnorm_succ, pow_succ', MulAut.mul_apply]
    congr 1
    have hu : (θ⁻¹ ^ i) ((θ ^ i) u) = u := by
      rw [← MulAut.mul_apply, inv_pow, inv_mul_cancel, MulAut.one_apply]
    have : (θ⁻¹ ^ i) (((tnorm θ i u) * (θ ^ i) u)⁻¹ * x * ((tnorm θ i u) * (θ ^ i) u)) =
        ((θ⁻¹ ^ i) ((θ ^ i) u))⁻¹ * (θ⁻¹ ^ i) ((tnorm θ i u)⁻¹ * x * tnorm θ i u) *
          (θ⁻¹ ^ i) ((θ ^ i) u) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      simp only [mul_inv_rev, mul_assoc]
    rw [this, hu]

theorem iterate_twist_mul (θ : MulAut G) {l : ℕ} (hθ : θ ^ l = 1) (u : G) (m : ℕ) (x : G) :
    (fun y => θ⁻¹ (u⁻¹ * y * u))^[l * m] x =
      (tnorm θ l u ^ m)⁻¹ * x * tnorm θ l u ^ m := by
  have hl : ∀ y, (fun y => θ⁻¹ (u⁻¹ * y * u))^[l] y = (tnorm θ l u)⁻¹ * y * tnorm θ l u := by
    intro y
    rw [iterate_twist, inv_pow, hθ]
    simp
  rw [Function.iterate_mul]
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, hl, pow_succ]
    group

theorem continuous_inv_of_pow_eq_one [TopologicalSpace G] {θ : MulAut G} (hc : Continuous θ)
    {l : ℕ} (hl : 0 < l) (hθ : θ ^ l = 1) : Continuous (θ⁻¹ : MulAut G) := by
  have hp : ∀ i : ℕ, Continuous (θ ^ i : MulAut G) := by
    intro i
    induction i with
    | zero => simpa using continuous_id
    | succ i ih =>
      rw [pow_succ']
      exact hc.comp ih
  have : θ⁻¹ = θ ^ (l - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hl, hθ]
  rw [this]
  exact hp _

theorem exists_twist_of_contract [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (J L T : Subgroup G) (hJ : IsCompact (J : Set G)) (θ : MulAut G) (hθc : Continuous θ) {l : ℕ}
    (hl : 0 < l) (hθl : θ ^ l = 1) (hθJ : J.map θ.toMonoidHom = J) (hθL : L.map θ.toMonoidHom = L)
    (hθT : T.map θ.toMonoidHom = T) (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hTL : ∀ s ∈ T, ∀ n ∈ L, s⁻¹ * n * s ∈ L) {t : G} (htT : t ∈ T)
    (htd : ∀ n ∈ J ⊓ L, t⁻¹ * n * t ∈ J ⊓ L)
    (hnd : ∀ n ∈ J ⊓ L, (tnorm θ l t)⁻¹ * n * tnorm θ l t ∈ J ⊓ L)
    (hns : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ j : ℕ, ∀ n ∈ J ⊓ L, (tnorm θ l t ^ j)⁻¹ * n * tnorm θ l t ^ j ∈ U)
    {a τ : G} (ha : a ∈ J ⊓ L) (hτ : τ ∈ J ⊓ T) :
    ∃ v ∈ J, v⁻¹ * (t * a * τ) * θ v = t * τ := by
  have hconj : ∀ s ∈ J ⊓ T, ∀ n ∈ J ⊓ L, s⁻¹ * n * s ∈ J ⊓ L := fun s hs n hn =>
    ⟨J.mul_mem (J.mul_mem (J.inv_mem hs.1) hn.1) hs.1, hTL s hs.2 n hn.2⟩
  have hθS : ∀ x ∈ J ⊓ L, θ⁻¹ x ∈ J ⊓ L := fun x hx =>
    ⟨inv_apply_mem hθJ hx.1, inv_apply_mem hθL hx.2⟩
  have hcinv := continuous_inv_of_pow_eq_one hθc hl hθl

  let Ψ : G → G := fun x => θ⁻¹ (τ⁻¹ * (a⁻¹ * (t⁻¹ * x * t)) * τ)
  let φ : G → G := fun x => θ⁻¹ ((t * τ)⁻¹ * x * (t * τ))
  have hΨc : Continuous Ψ := hcinv.comp (by fun_prop)
  have hΨS : ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), Ψ x ∈ ((J ⊓ L : Subgroup G) : Set G) :=
    fun x hx => hθS _ (hconj τ hτ _ ((J ⊓ L).mul_mem ((J ⊓ L).inv_mem ha) (htd x hx)))
  have hφS : ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), φ x ∈ ((J ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    refine hθS _ ?_
    have : (t * τ)⁻¹ * x * (t * τ) = τ⁻¹ * (t⁻¹ * x * t) * τ := by group
    rw [this]
    exact hconj τ hτ _ (htd x hx)
  have hid : ∀ x y, (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y) := by
    intro x y
    show (θ⁻¹ _)⁻¹ * θ⁻¹ _ = θ⁻¹ _
    rw [← map_inv, ← map_mul]
    congr 1
    group
  have hc : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), φ^[l * m] x ∈ U := by
    intro U hU h1
    obtain ⟨j, hj⟩ := hns U hU h1
    refine ⟨j, fun m hm x hx => ?_⟩
    set n := tnorm θ l t with hn
    set τ' := tnorm θ l τ with hτ'
    have hnT : n ∈ T := tnorm_mem hθT l htT
    have hτ'S : τ' ∈ J ⊓ T := ⟨tnorm_mem hθJ l hτ.1, tnorm_mem hθT l hτ.2⟩
    have hw : tnorm θ l (t * τ) = τ' * n := by
      rw [tnorm_mul_of_comm hθT hTc l htT hτ.2, hTc _ hnT _ hτ'S.2]
    have hcomm : Commute τ' n := hTc _ hτ'S.2 _ hnT
    have hiter := iterate_twist_mul θ hθl (t * τ) m x
    have hφ : φ^[l * m] x = (n ^ m)⁻¹ * ((τ' ^ m)⁻¹ * x * τ' ^ m) * n ^ m := by
      refine hiter.trans ?_
      rw [hw, hcomm.mul_pow]
      group
    rw [hφ]
    have hy : (τ' ^ m)⁻¹ * x * τ' ^ m ∈ J ⊓ L :=
      hconj _ ⟨J.pow_mem hτ'S.1 m, T.pow_mem hτ'S.2 m⟩ x hx
    have hdom : ∀ p : ℕ, ∀ y ∈ J ⊓ L, (n ^ p)⁻¹ * y * n ^ p ∈ J ⊓ L := by
      intro p
      induction p with
      | zero => intro y hy; simpa using hy
      | succ p ih =>
        intro y hy
        have := hnd _ (ih y hy)
        have e : (n ^ (p + 1))⁻¹ * y * n ^ (p + 1) = n⁻¹ * ((n ^ p)⁻¹ * y * n ^ p) * n := by
          rw [pow_succ]
          group
        rw [e]
        exact this
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hm
    have e : (n ^ (j + p))⁻¹ * ((τ' ^ (j + p))⁻¹ * x * τ' ^ (j + p)) * n ^ (j + p) =
        (n ^ j)⁻¹ * ((n ^ p)⁻¹ * ((τ' ^ (j + p))⁻¹ * x * τ' ^ (j + p)) * n ^ p) * n ^ j := by
      rw [pow_add n j p, (Commute.pow_pow_self n j p).eq]
      group
    rw [e]
    exact hj _ (hdom p _ hy)
  obtain ⟨v, hvJ, hv⟩ := exists_fixed_of_contract (K := (J : Set G))
    (S := ((J ⊓ L : Subgroup G) : Set G)) hJ (fun x hx => hx.1) (J ⊓ L).one_mem hΨc hΨS hφS hid hl hc
  refine ⟨v, hvJ, ?_⟩
  have hθv : θ v = τ⁻¹ * (a⁻¹ * (t⁻¹ * v * t)) * τ := by
    conv_lhs => rw [← hv]
    show θ (θ⁻¹ _) = _
    simp
  rw [hθv]
  group

end Generic

section Torus

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tor_comm (N : ℕ) : ∀ x ∈ Tor k N, ∀ y ∈ Tor k N, x * y = y * x := by
  rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  funext a
  apply Units.ext
  ext i j
  have hs : Subsingleton (Fin (ones N a)) := by unfold ones; infer_instance
  obtain rfl : i = j := Subsingleton.elim _ _
  show ((s a).val * (s' a).val) i i = ((s' a).val * (s a).val) i i
  simp only [Matrix.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]

theorem tor_conj_nlo (N : ℕ) : ∀ s ∈ Tor k N, ∀ n ∈ Nlo k N, s⁻¹ * n * s ∈ Nlo k N := by
  rintro _ ⟨s, rfl⟩ n hn
  have h := Subgroup.inv_mem _ (leviEmb_mem_normalizer_lower k (stdBlocks (ones N) (sum_ones N)) s)
  have := (Subgroup.mem_normalizer_iff.1 h n).1 hn
  rw [inv_inv] at this
  exact this

theorem killNlo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k)
    (hA : admitted k N J θ l) (hT : GoodT k N J θ l t) :
    ∀ a ∈ J ⊓ Nlo k N, ∀ τ ∈ J ⊓ Tor k N, ∃ j ∈ J, ∃ κ ∈ J ⊓ Tor k N,
      j⁻¹ * (t * a * τ) * θ j = t * κ := by
  obtain ⟨-, hJc, -, hθc, hl, hθl, hθJ, -, hθL, hθT⟩ := hA
  obtain ⟨htT, hdom, hstr⟩ := hT
  intro a ha τ hτ
  obtain ⟨s, hs, hsd⟩ := hdom 0 hl
  obtain ⟨s', hs', hsd', hc⟩ := hstr
  have ht0 : torEmb k N s = t := by simpa using hs
  have htd : ∀ n ∈ J ⊓ Nlo k N, t⁻¹ * n * t ∈ J ⊓ Nlo k N := by
    intro n hn
    rw [← ht0]
    exact hsd.2.1 n hn
  have hnd : ∀ n ∈ J ⊓ Nlo k N, (tnorm θ l t)⁻¹ * n * tnorm θ l t ∈ J ⊓ Nlo k N := by
    intro n hn
    rw [← hs']
    exact hsd'.1.2.1 n hn
  obtain ⟨v, hvJ, hv⟩ := exists_twist_of_contract J (Nlo k N) (Tor k N) hJc θ hθc hl hθl hθJ hθL hθT
    (tor_comm N) (tor_conj_nlo N) htT htd hnd hc ha hτ
  exact ⟨v, hvJ, τ, hτ, hv⟩

end Torus

end GlobalTheory.CompanionTheory.Lbc.KillNlo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTorusCommutative
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.TorComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones_eq (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    simp only [ones] at this
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [ones, hi]

theorem offDiag_of_mem {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  rw [Tor, MonoidHom.mem_range] at hx
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective j
  have hab : a ≠ b := by
    rintro rfl
    apply hij
    have hp : (p : ℕ) = 0 := by
      have := p.isLt
      simp only [ones] at this
      omega
    have hq : (q : ℕ) = 0 := by
      have := q.isLt
      simp only [ones] at this
      omega
    have hpq : p = q := Fin.ext (hp.trans hq.symm)
    rw [hpq]
  exact leviEmb_apply_ne k _ s hab p q

theorem diag_ne_zero {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  have hM : (x : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun l => (x : Matrix (Fin N) (Fin N) k) l l := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact h a b hab
  have hdet : (x : Matrix (Fin N) (Fin N) k).det ≠ 0 := (Matrix.isUnits_det_units x).ne_zero
  rw [hM, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem mem_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  rw [Tor, MonoidHom.mem_range]
  refine ⟨(fun a => Matrix.GeneralLinearGroup.scalar _
    (Units.mk0 ((x : Matrix (Fin N) (Fin N) k) a a) (diag_ne_zero x h a)) : Levi k (Bl (ones N))), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective j
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := by
      apply Fin.ext
      have hp := p.isLt
      have hq := q.isLt
      simp only [ones] at hp hq
      omega
    subst hpq
    refine (leviEmb_apply_same (m := fun c => Fin (ones N c)) k _ _ a p p).trans ?_
    rw [stdBlocks_ones_eq N a p]
    simp [Matrix.GeneralLinearGroup.scalar]
  · rw [h _ _ (fun heq => hab (congrArg Sigma.fst ((stdBlocks (ones N) (sum_ones N)).injective heq)))]
    exact leviEmb_apply_ne (m := fun c => Fin (ones N c)) k _ _ hab p q

theorem eq_diagonal {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact h a b hab

theorem mul_comm_of_mem {N : ℕ} {a b : GL (Fin N) k} (ha : a ∈ Tor k N) (hb : b ∈ Tor k N) :
    a * b = b * a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    eq_diagonal (a : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem ha hij),
    eq_diagonal (b : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem hb hij),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem tor_comm_and_mem_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ),
    (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧
      ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔
        ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  intro k _ _ _ _ N
  exact ⟨fun a ha b hb => mul_comm_of_mem ha hb,
    fun x => ⟨fun hx i j hij => offDiag_of_mem hx hij, mem_of_offDiag x⟩⟩

end GlobalTheory.CompanionTheory.LbElem.TorComm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompactStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_open_subgroup_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) → ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧ (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧ ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  first | exact @GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | exact GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | (intros; apply GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO <;> assumption)
end

