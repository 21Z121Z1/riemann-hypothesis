import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.HasElemDiv

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDualImports
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.ThetaUniq

def cosetInd (F : Type) [Field F] [NumberField F] {κ : Type} (N : ℕ) (d : κ → F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator {x | ∀ i, ∃ u : FiniteAdeleRing (𝓞 F) F, (∀ v, u v ∈ v.adicCompletionIntegers F) ∧
    x i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i) + N • u} 1

end GlobalTheory.CompanionTheory.ThetaUniq

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsInvariantForm
section
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.LagFun

theorem exists_param {k : Type} [Field k] {κ : Type} [Fintype κ] (large₂ : Submodule k ((κ → k) × (κ → k))) :
    ∃ (n : ℕ) (j σ : (Fin n → k) →ₗ[k] (κ → k)) (p : (κ → k) →ₗ[k] (Fin n → k)),
      (∀ t, p (j t) = t) ∧ (∀ t, (j t, σ t) ∈ large₂) ∧ ∀ w ∈ large₂, ∃ t, j t = w.1 := by
  set f : large₂ →ₗ[k] (κ → k) := LinearMap.fst k _ _ ∘ₗ large₂.subtype with hf
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  set e := (Module.finBasis k (LinearMap.range f)).equivFun.symm
  set j := (LinearMap.range f).subtype ∘ₗ e.toLinearMap with hj
  have hinj : LinearMap.ker j = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp e.injective
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective hinj
  refine ⟨_, j, LinearMap.snd k _ _ ∘ₗ large₂.subtype ∘ₗ s ∘ₗ e.toLinearMap, p, fun t => LinearMap.congr_fun hp t,
    fun t => ?_, fun w hw => ⟨e.symm ⟨w.1, ⟨w, hw⟩, rfl⟩, by simp [hj]⟩⟩
  have h1 : (s (e t) : (κ → k) × (κ → k)).1 = j t := congrArg Subtype.val (LinearMap.congr_fun hs (e t))
  rw [← h1]
  exact (s (e t)).2

theorem exists_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ), Continuous ψ → ψ ≠ 1 → ∀ large₂ : Submodule k ((κ → k) × (κ → k)), (∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) → ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), l φ ≠ 0) ∧ ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ := by
  intro k _ _ _ _ _ κ _ ψ hψ _ large₂ hL
  obtain ⟨n, j, σ, p, hp, hσ, hj⟩ := exists_param large₂
  have hT2 : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hlc : LocallyCompactSpace k := inferInstance
  have htd : TotallyDisconnectedSpace k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    have : NonarchimedeanAddGroup k := ⟨fun U hU => by
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
      exact ⟨⟨(Valued.v (R := k)).restrict.ltAddSubgroup γ, by
        simpa [Valuation.ltAddSubgroup] using Valued.isOpen_ball k γ⟩, hγ⟩⟩
    infer_instance
  let : MeasurableSpace (Fin n → k) := borel _
  have : BorelSpace (Fin n → k) := ⟨rfl⟩
  set μ : Measure (Fin n → k) := Measure.addHaar
  have cj : Continuous j := j.continuous_on_pi
  have cσ : Continuous σ := σ.continuous_on_pi
  have cp : Continuous p := p.continuous_on_pi
  have hce : Topology.IsClosedEmbedding j := Function.LeftInverse.isClosedEmbedding hp cp cj
  set g : (Fin n → k) → ℂ := fun t => ψ (⅟(2 : k) * (j t ⬝ᵥ σ t)) with hg
  have cg : Continuous g := hψ.comp (continuous_const.mul (cj.dotProduct cσ))
  set S : Submodule ℂ ((κ → k) → ℂ) :=
    { carrier := {φ | Integrable (fun t => g t * φ (j t)) μ}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add]
        exact Integrable.add ha hb
      smul_mem' := fun c a ha => by
        simpa only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm] using Integrable.const_mul ha c }
  have memS : ∀ φ, φ ∈ S ↔ Integrable (fun t => g t * φ (j t)) μ := fun _ => Iff.rfl
  set l₀ : S →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ t, g t * φ.1 (j t) ∂μ
      map_add' := fun a b => by
        rw [← integral_add a.2 b.2]
        simp [mul_add]
      map_smul' := fun c a => by
        simp [← integral_const_mul, mul_left_comm] }
  obtain ⟨l, hl⟩ := l₀.exists_extend
  have hl' : ∀ φ ∈ S, l φ = ∫ t, g t * φ (j t) ∂μ := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  have cc : ∀ φ ∈ SB (κ → k), Continuous (fun t => g t * φ (j t)) ∧ HasCompactSupport (fun t => g t * φ (j t)) :=
    fun φ hφ => ⟨cg.mul (hφ.1.continuous.comp cj), (hφ.2.comp_isClosedEmbedding hce).mul_left⟩
  have hSB : ∀ φ ∈ SB (κ → k), φ ∈ S := fun φ hφ => (cc φ hφ).1.integrable_of_hasCompactSupport (cc φ hφ).2
  refine ⟨l, ?_, fun w hw φ hφ => ?_⟩
  · have ho : IsOpen {x : κ → k | 0 < (g (p x)).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (cg.comp cp))
    have h0 : (0 : κ → k) ∈ {x : κ → k | 0 < (g (p x)).re} := by simp [hg]
    obtain ⟨K, hK, hK0, hKs⟩ := exists_compact_subset ho h0
    obtain ⟨U, hU, hU0, hUs⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := κ → k)).exists_subset_of_mem_open hK0
      isOpen_interior
    have hU : IsClopen U := hU
    have hUK : U ⊆ K := hUs.trans interior_subset
    have hφ : U.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → k) :=
      ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hU).isLocallyConstant,
        HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem (fun h => hx (hUK h)) _⟩
    refine ⟨_, hφ, fun h => ?_⟩
    rw [hl' _ (hSB _ hφ)] at h
    have h2 := congrArg Complex.re h
    rw [← RCLike.re_to_complex, ← integral_re ((memS _).1 (hSB _ hφ))] at h2
    refine ne_of_gt ?_ h2
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (RCLike.continuous_re.comp (cc _ hφ).1) ((cc _ hφ).2.comp_left (g := RCLike.re) (map_zero _)) (fun t => ?_) ?_
    · by_cases ht : j t ∈ U
      · have := hKs (hUK ht)
        simp only [Set.mem_ofPred_eq, hp] at this
        simpa [ht] using this.le
      · simp [ht]
    · simp [hU0, hg]
  · obtain ⟨t₁, ht₁⟩ := hj w hw
    have key : (fun t => g t * schr ψ w φ (j t)) = fun t => g (t + t₁) * φ (j (t + t₁)) := by
      funext t
      have e1 := hL _ (hσ t) w hw
      have e2 := hL _ (hσ t₁) w hw
      have e3 := hL _ (hσ t) _ (hσ t₁)
      simp only [← ht₁] at e1 e2 e3
      simp only [hg, schr, ← ht₁, map_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
      congr 2
      have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
      linear_combination e1 + ⅟(2 : k) * e2 - ⅟(2 : k) * e3 - (j t₁ ⬝ᵥ σ t) * h2
    have hi := (memS _).1 (hSB _ hφ)
    rw [hl' _ (hSB _ hφ), hl' _ ((memS _).2 (key ▸ hi.comp_add_right t₁)), key]
    exact integral_add_right_eq_self (fun t => g t * φ (j t)) t₁

end GlobalTheory.CompanionTheory.LagFun
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsArtinianRingKummerAdjoinRootQuotientRoot
section
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitRow.IdxV

theorem relIndex_pi' {ι G : Type} [Fintype ι] [AddCommGroup G] (H K : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) = ∏ i, (H i).relIndex (K i) := by
  let f : (∀ i, K i) →+ (ι → G) :=
    { toFun := fun x i => (x i : G), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h1 : AddSubgroup.pi Set.univ K = (⊤ : AddSubgroup (∀ i, K i)).map f := by
    ext x
    simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_true_left, AddSubgroup.mem_map,
      AddSubgroup.mem_top, true_and]
    exact ⟨fun h => ⟨fun i => ⟨x i, h i⟩, rfl⟩, by rintro ⟨y, rfl⟩ i; exact (y i).2⟩
  rw [h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right]
  simp only [AddSubgroup.relIndex]
  simp only [AddSubgroup.index]
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight fun x y => ?_).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_apply]
  refine forall_congr' fun i => ?_
  exact ⟨fun h => QuotientAddGroup.leftRel_apply.2 (h trivial), fun h _ =>
    (QuotientAddGroup.leftRel_apply (s := (H i).addSubgroupOf (K i))).1 h⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ball (c : k) : AddSubgroup k := (𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulRight c)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_ball (c x : k) : x ∈ ball c ↔ x * c ∈ 𝒪[k] := Iff.rfl

theorem relIndex_ball (ϖ : kˣ) (hϖ : ∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ) (b : ℤ) :
    (ball (1 : k)).relIndex (ball ((ϖ ^ b : kˣ) : k)) = resCard k ^ b.toNat := by
  obtain ⟨p, hp, hpϖ⟩ := hϖ
  have hne : (ϖ : k) ≠ 0 := ϖ.ne_zero
  obtain ⟨m, rfl | rfl⟩ := b.eq_nat_or_neg
  · let f : 𝒪[k] →+ k := (AddMonoidHom.mulRight (((ϖ : k) ^ m)⁻¹)).comp (𝒪[k]).subtype.toAddMonoidHom
    have hf : ∀ x, f x = (x : k) * ((ϖ : k) ^ m)⁻¹ := fun _ => rfl
    have h1 : ball ((ϖ ^ (m : ℤ) : kˣ) : k) = (⊤ : AddSubgroup 𝒪[k]).map f := by
      ext x
      simp only [mem_ball, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, hf, zpow_natCast,
        Units.val_pow_eq_pow_val]
      constructor
      · intro h
        exact ⟨⟨_, h⟩, by field_simp⟩
      · rintro ⟨y, rfl⟩
        rw [inv_mul_cancel_right₀ (pow_ne_zero _ hne)]
        exact y.2
    have h2 : (ball (1 : k)).comap f = ((IsLocalRing.maximalIdeal 𝒪[k]) ^ m).toAddSubgroup := by
      ext x
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp, Ideal.span_singleton_pow,
        AddSubgroup.mem_comap, mem_ball, hf, mul_one, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
      constructor
      · intro h
        refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
        push_cast
        rw [hpϖ]; field_simp
      · rintro ⟨y, rfl⟩
        push_cast
        rw [hpϖ, mul_inv_cancel_right₀ (pow_ne_zero _ hne)]
        exact y.2
    rw [h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, h2, Int.toNat_natCast]
    exact cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝒪[k])
  · rw [Int.toNat_neg_natCast, pow_zero, AddSubgroup.relIndex_eq_one]
    intro x hx
    rw [mem_ball] at hx ⊢
    have : x * 1 = x * ((ϖ ^ (-(m : ℤ)) : kˣ) : k) * ((p ^ m : 𝒪[k]) : k) := by
      push_cast
      rw [hpϖ]
      simp only [_root_.zpow_neg, zpow_natCast]
      field_simp
    rw [this]
    exact mul_mem hx (p ^ m).2

variable {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]

end GlobalTheory.CompanionTheory.SplitRow.IdxV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumStarAndSchAStar
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.ThetaReal

theorem thetaSum_star_and_schA_star (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    thetaSum F (star Φ) = conj (thetaSum F Φ) ∧ (Φ ∈ schA F κ → star Φ ∈ schA F κ) := by
  refine ⟨?_, fun h => ?_⟩
  · unfold thetaSum
    rw [← RCLike.star_def, tsum_star]
    rfl
  · classical
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      refine Submodule.subset_span ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, star g,
        ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩, ?_⟩
      funext x
      simp [pureA]
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.ThetaReal
end

