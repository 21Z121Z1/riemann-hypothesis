import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CardZBasisEqMulFinrank
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DiffLatStep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section Step

variable {Em K : Type} [Field Em] [NumberField Em] [Field K] [NumberField K] {N : ℕ}

theorem absNorm_map_mapRingHom (s : Em →+* K) (b : Ideal (𝓞 Em)) :
    letI : Algebra Em K := s.toAlgebra
    Ideal.absNorm (b.map (RingOfIntegers.mapRingHom s)) = Ideal.absNorm b ^ Module.finrank Em K := by
  let _ : Algebra Em K := s.toAlgebra
  have h1 : RingOfIntegers.mapRingHom s = algebraMap (𝓞 Em) (𝓞 K) := rfl
  have h3 : Module.finrank (𝓞 Em) (𝓞 K) = Module.finrank Em K :=
    (IsFractionRing.finrank_eq (𝓞 Em) Em (𝓞 K) K).symm
  rw [h1, Ideal.absNorm_algebraMap, h3]

omit [NumberField Em] in

theorem span_singleton_toAddSubgroup (x : Fin N → Em) :
    (Submodule.span (𝓞 Em) {x}).toAddSubgroup =
      (⊤ : AddSubgroup (𝓞 Em)).map (LinearMap.toSpanSingleton (𝓞 Em) _ x).toAddMonoidHom := by
  ext y
  simp [Submodule.mem_span_singleton]

omit [NumberField K] in
theorem map_toAddSubgroup' (f : 𝓞 K →ₗ[𝓞 K] (Fin N → K)) (D : Ideal (𝓞 K)) :
    (Submodule.map f D).toAddSubgroup = D.toAddSubgroup.map f.toAddMonoidHom := by
  ext y
  simp

theorem relIndex_mul_ideal {F : Type} [Field F] [NumberField F] (D B : Ideal (𝓞 F)) (hD : Ideal.absNorm D ≠ 0) :
    (D * B).toAddSubgroup.relIndex D.toAddSubgroup = Ideal.absNorm B := by
  have h := AddSubgroup.relIndex_mul_index (H := (D * B).toAddSubgroup) (K := D.toAddSubgroup)
    (Submodule.toAddSubgroup_mono Ideal.mul_le_left)
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, map_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hD) (by rw [h, mul_comm])

theorem diffLat_step (s : Em →+* K) (P : Submodule (𝓞 Em) (Fin N → Em)) (x : Fin N → Em)
    (hP : P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0) :
    letI : Algebra Em K := s.toAlgebra
    (diffLat s P).toAddSubgroup.relIndex (diffLat s (P ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup ≤
      P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ^ Module.finrank Em K := by
  let _ : Algebra Em K := s.toAlgebra
  let g : 𝓞 Em →ₗ[𝓞 Em] (Fin N → Em) := LinearMap.toSpanSingleton (𝓞 Em) _ x
  let f : 𝓞 K →ₗ[𝓞 K] (Fin N → K) := LinearMap.toSpanSingleton (𝓞 K) _ (fun i => s (x i))
  let b : Ideal (𝓞 Em) := P.comap g
  have hPQ : P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup = Ideal.absNorm b := by
    rw [Submodule.sup_toAddSubgroup, span_singleton_toAddSubgroup, AddSubgroup.relIndex_sup_left,
      ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, Ideal.absNorm_eq_index]
    rfl
  have hXQ : diffLat s (P ⊔ Submodule.span (𝓞 Em) {x}) =
      diffLat s P ⊔ Submodule.map f (extDifferent s) := by
    apply le_antisymm
    · rw [diffLat, Submodule.span_le]
      rintro _ ⟨u, ⟨y, hy, z, hz, rfl⟩, rfl⟩
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq
      have e : (fun i => s (((y : Em) • (p + c • x)) i)) =
          (fun i => s (((y : Em) • p) i)) + f (RingOfIntegers.mapRingHom s (y * c)) := by
        funext i
        simp [f, Algebra.smul_def, mul_add, mul_assoc]
      show (fun i => s (((y : Em) • (p + c • x)) i)) ∈ _
      rw [e]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨y, hy, p, hp, rfl⟩, rfl⟩)
        (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_right c _ hy)))
    · refine sup_le (diffLat_mono s le_sup_left) ?_
      rw [Submodule.map_le_iff_le_comap, extDifferent, Ideal.map_le_iff_le_comap]
      intro y hy
      simp only [Ideal.mem_comap, Submodule.mem_comap, f, LinearMap.toSpanSingleton_apply]
      apply Submodule.subset_span
      refine ⟨(y : Em) • x, ⟨y, hy, x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x), rfl⟩, ?_⟩
      funext i
      simp [Algebra.smul_def]
  have h1 : (diffLat s P).toAddSubgroup.relIndex (diffLat s (P ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup =
      ((diffLat s P).toAddSubgroup.comap f.toAddMonoidHom).relIndex (extDifferent s).toAddSubgroup := by
    rw [hXQ, Submodule.sup_toAddSubgroup, map_toAddSubgroup', AddSubgroup.relIndex_sup_left,
      AddSubgroup.relIndex_comap]
  have h2 : extDifferent s * b.map (RingOfIntegers.mapRingHom s) ≤ (diffLat s P).comap f := by
    rw [extDifferent, ← Ideal.map_mul, Ideal.map_le_iff_le_comap]
    refine Ideal.mul_le.2 fun y hy c hc => ?_
    have hc' : c • x ∈ P := hc
    simp only [Ideal.mem_comap, Submodule.mem_comap, f, LinearMap.toSpanSingleton_apply]
    apply Submodule.subset_span
    refine ⟨(y : Em) • (c • x), ⟨y, hy, c • x, hc', rfl⟩, ?_⟩
    funext i
    simp [Algebra.smul_def, mul_assoc]
  have hD : Ideal.absNorm (extDifferent s) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact extDifferent_ne_bot s
  have h3 : (extDifferent s * b.map (RingOfIntegers.mapRingHom s)).toAddSubgroup.relIndex
      (extDifferent s).toAddSubgroup = Ideal.absNorm (b.map (RingOfIntegers.mapRingHom s)) := by
    exact relIndex_mul_ideal _ _ hD
  have h4 := absNorm_map_mapRingHom s b
  rw [h1, hPQ, ← h4, ← h3]
  refine AddSubgroup.relIndex_le_of_le_left (fun z hz => h2 hz) ?_
  rw [h3, h4]
  exact pow_ne_zero _ (hPQ ▸ hP)

theorem diffLat_relIndex_le (s : Em →+* K) {M' M : Submodule (𝓞 Em) (Fin N → Em)} (hle : M' ≤ M) (hfg : M.FG)
    (hM : M'.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) :
    letI : Algebra Em K := s.toAlgebra
    (diffLat s M').toAddSubgroup.relIndex (diffLat s M).toAddSubgroup ≤
      M'.toAddSubgroup.relIndex M.toAddSubgroup ^ Module.finrank Em K := by
  classical
  let _ : Algebra Em K := s.toAlgebra
  obtain ⟨T, hT⟩ := hfg
  have hTM : (↑T : Set (Fin N → Em)) ⊆ M := hT ▸ Submodule.subset_span
  have key : ∀ T : Finset (Fin N → Em), (↑T : Set (Fin N → Em)) ⊆ M →
      (diffLat s M').toAddSubgroup.relIndex (diffLat s (M' ⊔ Submodule.span (𝓞 Em) ↑T)).toAddSubgroup ≤
        M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup ^ Module.finrank Em K := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert x T hx ih =>
      intro hT'
      have hxM : x ∈ M := hT' (Finset.mem_insert_self _ _)
      have hTM' : (↑T : Set (Fin N → Em)) ⊆ M := fun y hy => hT' (Finset.mem_insert_of_mem hy)
      have hPeq : M' ⊔ Submodule.span (𝓞 Em) ↑(insert x T) =
          (M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x} := by
        rw [Finset.coe_insert, Submodule.span_insert, sup_comm (Submodule.span (𝓞 Em) {x}), ← sup_assoc]
      rw [hPeq]
      have hP_le : M' ⊔ Submodule.span (𝓞 Em) ↑T ≤ M := sup_le hle (Submodule.span_le.2 hTM')
      have hPx_le : (M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x} ≤ M :=
        sup_le hP_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hxM))
      have hne : M'.toAddSubgroup.relIndex
          ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0 :=
        fun h => hM (AddSubgroup.relIndex_eq_zero_of_le_right hPx_le h)
      have hmul := AddSubgroup.relIndex_mul_relIndex M'.toAddSubgroup
        (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup
        ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup
        (le_sup_left : M' ≤ _) (le_sup_left : M' ⊔ Submodule.span (𝓞 Em) ↑T ≤ _)
      have hstep : (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup.relIndex
          ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0 :=
        fun h => hne (by rw [← hmul, h, mul_zero])
      have hX := AddSubgroup.relIndex_mul_relIndex (diffLat s M').toAddSubgroup
        (diffLat s (M' ⊔ Submodule.span (𝓞 Em) ↑T)).toAddSubgroup
        (diffLat s ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup
        (diffLat_mono s le_sup_left) (diffLat_mono s le_sup_left)
      rw [← hX, ← hmul, mul_pow]
      exact Nat.mul_le_mul (ih hTM') (diffLat_step s _ x hstep)
  have hM_eq : M = M' ⊔ Submodule.span (𝓞 Em) ↑T := by rw [hT, sup_eq_right.2 (hT ▸ hle)]
  rw [hM_eq] at hM ⊢
  exact key T hTM

end Step

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ExistsIsZBasisOfLe
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Module
open scoped Matrix

theorem exists_isZBasis_of_le {Em : Type} [Field Em] [NumberField Em] {N : ℕ}
    {I L : Submodule (𝓞 Em) (Fin N → Em)} (hIL : I ≤ L) (hfg : (L.restrictScalars ℤ).FG) :
    ∃ m, ∃ b : Fin m → Fin N → Em, IsZBasis I b := by
  have hle : I.restrictScalars ℤ ≤ L.restrictScalars ℤ := hIL
  haveI : Module.Finite ℤ (L.restrictScalars ℤ) := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ (I.restrictScalars ℤ) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  let bI := Module.finBasis ℤ (I.restrictScalars ℤ)
  refine ⟨_, fun k => (bI k : Fin N → Em), ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact bI.linearIndependent.map' (I.restrictScalars ℤ).subtype (Submodule.ker_subtype _)
  · have h := congrArg Subtype.val (bI.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have hsp : Submodule.span ℤ (Set.range fun k => (bI k : Fin N → Em)) ≤ I.restrictScalars ℤ :=
      Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (bI k).2)
    exact hsp hx

theorem UnitaryCovolume.proof : UnitaryCovolume.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D z hz I hIL hI _ ρ v hv
  have hex := exists_isZBasis_of_le hIL D.herm.fg
  have hnz : ∃ ρ' v', IsNzFamily I ρ' v' := ⟨ρ, v, hv⟩
  have hn := D.herm.finrank_eq_two_mul_card_cm
  have hpos : 0 < finrank ℚ Em := Module.finrank_pos
  have key : ∀ ρ' (v' : Fin ρ' → Fin D.N → Em), IsNzFamily I ρ' v' →
      D.covolZ z I = (∏ τ, (D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v').det.re) /
          ((Submodule.span (𝓞 Em) (Set.range v')).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) *
        rootDiscr Em ^ (D.f * ρ) := by
    intro ρ' v' hv'
    obtain ⟨m, b, hb⟩ := hex
    have h1 := card_zBasis_eq_mul_finrank hv hb
    have h2 := card_zBasis_eq_mul_finrank hv' hb
    have hρ : ρ' = ρ := Nat.eq_of_mul_eq_mul_right hpos (h2.symm.trans h1)
    subst hρ
    rw [D.covolZ_eq_of_family hz hI hv' ⟨m, b, hb⟩]
    congr 1
    rw [rootDiscr, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hn]
    congr 1
    have hf : D.f = Fintype.card Ψ := rfl
    have hc : (Fintype.card Ψ : ℝ) ≠ 0 := by
      have : 0 < Fintype.card Ψ := by omega
      positivity
    rw [hf]
    push_cast
    field_simp
  unfold FullerData.nz HermDatum.nz
  rw [dif_pos hnz]
  exact key _ _ hnz.choose_spec.choose_spec

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcChartSemipos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def MUcChartSemipos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (S : BoundedRegularisationSetting M D.Xo H.aMu w),
    ∃ c : ℝ, 0 < c ∧ ∀ (B p q : ℕ) (t δ : ℝ),
      M.atlas.Smooth (S.bregWeight t) →
      (∀ k : Fin S.B.N, ∀ x ∈ S.B.mid k, ∀ v : Fin D.n → ℂ,
        -δ * ‖v‖ ^ 2 ≤ levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k x) v) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (MUc H S B p q t)

section Inhabitants

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {H : HodgeData D} {M : XModel D}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
end
end

