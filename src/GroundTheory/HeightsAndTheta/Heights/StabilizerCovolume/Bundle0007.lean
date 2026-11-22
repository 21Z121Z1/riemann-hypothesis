import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DiffLatFree
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section IdealLat

variable {F : Type} [Field F] [NumberField F] {N ρ : ℕ}

def idealLat (w : Fin ρ → Fin N → F) (a : Ideal (𝓞 F)) : Submodule (𝓞 F) (Fin N → F) :=
  Submodule.map (Fintype.linearCombination (𝓞 F) w) (Submodule.pi Set.univ fun _ => a)

theorem linearCombination_injective {w : Fin ρ → Fin N → F} (hw : LinearIndependent F w) :
    Function.Injective (Fintype.linearCombination (𝓞 F) w) := by
  have hw' : LinearIndependent (𝓞 F) w := (LinearIndependent.iff_fractionRing (𝓞 F) F).2 hw
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  funext i
  exact Fintype.linearIndependent_iff.1 hw' c (by rwa [Fintype.linearCombination_apply] at hc) i

omit [NumberField F] in
theorem idealLat_toAddSubgroup (w : Fin ρ → Fin N → F) (a : Ideal (𝓞 F)) :
    (idealLat w a).toAddSubgroup = AddSubgroup.map (Fintype.linearCombination (𝓞 F) w).toAddMonoidHom
      (AddSubgroup.pi Set.univ fun _ => a.toAddSubgroup) := by
  ext x
  simp [idealLat, Submodule.mem_pi, AddSubgroup.mem_pi]

theorem idealLat_relIndex {w : Fin ρ → Fin N → F} (hw : LinearIndependent F w) {a b : Ideal (𝓞 F)}
    (hab : a ≤ b) :
    (idealLat w a).toAddSubgroup.relIndex (idealLat w b).toAddSubgroup * Ideal.absNorm b ^ ρ =
      Ideal.absNorm a ^ ρ := by
  rw [idealLat_toAddSubgroup, idealLat_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (linearCombination_injective hw)]
  have h := AddSubgroup.relIndex_mul_index (H := AddSubgroup.pi Set.univ fun _ : Fin ρ => a.toAddSubgroup)
    (K := AddSubgroup.pi Set.univ fun _ : Fin ρ => b.toAddSubgroup) (fun x hx i hi => hab (hx i hi))
  rw [AddSubgroup.index_pi, AddSubgroup.index_pi] at h
  simpa [Ideal.absNorm_eq_index] using h

omit [NumberField F] in

theorem idealLat_smul (w : Fin ρ → Fin N → F) (r : 𝓞 F) (a : Ideal (𝓞 F)) :
    idealLat (fun i => r • w i) a = idealLat w (Ideal.span {r} * a) := by
  ext x
  simp only [idealLat, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
    Fintype.linearCombination_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => r * c i, fun i => Ideal.mem_span_singleton_mul.2 ⟨c i, hc i, rfl⟩, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro ⟨c, hc, rfl⟩
    choose d hd hdc using fun i => Ideal.mem_span_singleton_mul.1 (hc i)
    refine ⟨d, hd, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← hdc i, smul_smul, mul_comm]

omit [NumberField F] in

theorem idealLat_top (w : Fin ρ → Fin N → F) :
    idealLat w ⊤ = Submodule.span (𝓞 F) (Set.range w) := by
  rw [idealLat, Submodule.pi_top, Submodule.map_top, Fintype.range_linearCombination]

end IdealLat

section DiffLatSpan

variable {Em K : Type} [Field Em] [NumberField Em] [Field K] [NumberField K] {N ρ : ℕ}

omit [NumberField K] in

theorem diffLat_mono (s : Em →+* K) {M M' : Submodule (𝓞 Em) (Fin N → Em)} (h : M ≤ M') :
    diffLat s M ≤ diffLat s M' :=
  Submodule.span_mono (Set.image_mono fun _ ⟨x, hx, y, hy, hu⟩ => ⟨x, hx, y, h hy, hu⟩)

theorem diffLat_span (s : Em →+* K) (w : Fin ρ → Fin N → Em) :
    diffLat s (Submodule.span (𝓞 Em) (Set.range w)) = idealLat (fun a i => s (w a i)) (extDifferent s) := by
  apply le_antisymm
  · rw [diffLat, Submodule.span_le]
    rintro _ ⟨u, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 hy
    refine ⟨fun a => RingOfIntegers.mapRingHom s (x * c a),
      fun a _ => Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ hx), ?_⟩
    funext i
    simp [Fintype.linearCombination_apply, Finset.sum_apply, map_sum, Algebra.smul_def, mul_assoc,
      Finset.mul_sum]
  · rw [idealLat, Submodule.map_le_iff_le_comap]
    intro c hc
    simp only [Submodule.mem_comap, Fintype.linearCombination_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    have key : extDifferent s ≤ (diffLat s (Submodule.span (𝓞 Em) (Set.range w))).comap
        (LinearMap.toSpanSingleton (𝓞 K) _ (fun i => s (w a i))) := by
      rw [extDifferent, Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      apply Submodule.subset_span
      refine ⟨(x : Em) • w a, ⟨x, hx, w a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
      funext i
      simp [Algebra.smul_def]
    exact key (hc a (Set.mem_univ a))

end DiffLatSpan

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.HodgeFrameInjective
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def embHom : (Fin D.N → Em) →+ ((Ψ × Fin D.N) → ℂ) where
  toFun v p := D.herm.emb p.1 (v p.2)
  map_zero' := by
    funext p
    simp
  map_add' v w := by
    funext p
    simp

def hodgeFrame (z : (Σ k, ι k) → ℂ) : ((Ψ × Fin D.N) → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin D.N) where
  toFun y := WithLp.toLp 2 fun p =>
    (Real.sqrt (2 * ‖D.herm.emb p.1 D.herm.ξ‖) : ℂ) * ((D.per z p.1)⁻¹ *ᵥ fun a => y (p.1, a)) p.2
  map_add' y y' := by
    ext p
    simp only [PiLp.add_apply, Pi.add_apply]
    rw [show (fun a => y (p.1, a) + y' (p.1, a)) = (fun a => y (p.1, a)) + fun a => y' (p.1, a) from rfl,
      Matrix.mulVec_add, Pi.add_apply, mul_add]
  map_smul' r y := by
    ext p
    simp only [PiLp.smul_apply, Pi.smul_apply, RingHom.id_apply]
    rw [show (fun a => r • y (p.1, a)) = r • fun a => y (p.1, a) from rfl, Matrix.mulVec_smul,
      Pi.smul_apply, Complex.real_smul, Complex.real_smul]
    ring

theorem inner_hodgeFrame (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) :
    inner ℝ (D.hodgeFrame z (D.embHom v)) (D.hodgeFrame z (D.embHom w)) = D.hodgeInner z v w := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, hodgeInner]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hodgeFrame, embHom, LinearMap.coe_mk, AddHom.coe_mk, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, WithLp.ofLp_toLp, Complex.inner, map_mul, Complex.conj_ofReal]
  have hs : Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) * Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) =
      2 * ‖D.herm.emb τ D.herm.ξ‖ := Real.mul_self_sqrt (by positivity)
  rw [show ∀ (s : ℝ) (u x : ℂ), (s * x * ((s : ℂ) * starRingEnd ℂ u)).re = (s * s) * (starRingEnd ℂ u * x).re by
    intro s u x
    rw [show (s : ℂ) * x * ((s : ℂ) * starRingEnd ℂ u) = ((s * s : ℝ) : ℂ) * (starRingEnd ℂ u * x) by
      push_cast
      ring, Complex.re_ofReal_mul], hs]

theorem hodgeFrame_injective {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) : Function.Injective (D.hodgeFrame z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  funext p
  obtain ⟨τ, a⟩ := p
  have hP : IsUnit (D.per z τ).det := FirstMinPos.isUnit_det_of_eq_signMat (D.per_witt z hz τ)
  have hs : (Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) : ℂ) ≠ 0 := by
    have : D.herm.emb τ D.herm.ξ ≠ 0 := (map_ne_zero _).2 D.herm.ξ_ne
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have h0 : (D.per z τ)⁻¹ *ᵥ (fun b => y (τ, b)) = 0 := by
    funext b
    have := congrArg (fun x : EuclideanSpace ℂ (Ψ × Fin D.N) => x (τ, b)) hy
    simp only [hodgeFrame, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, PiLp.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hs
  have h1 : (fun b => y (τ, b)) = 0 := by
    rw [← Matrix.one_mulVec (fun b => y (τ, b)), ← Matrix.mul_nonsing_inv _ hP, ← Matrix.mulVec_mulVec, h0,
      Matrix.mulVec_zero]
  exact congr_fun h1 a

end FullerData

theorem UnitaryMinkowskiBound.proof : UnitaryMinkowskiBound.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D z hz I hI ρ v hv
  classical
  have hex := D.herm.exists_isZBasis hI
  have hcov : D.covolZ z I = Real.sqrt (Matrix.of fun k l =>
      D.hodgeInner z (hex.choose_spec.choose k) (hex.choose_spec.choose l)).det := by
    unfold FullerData.covolZ
    rw [dif_pos hex]
  have hb : IsZBasis I hex.choose_spec.choose := hex.choose_spec.choose_spec
  have hm : hex.choose = 2 * D.f * ρ := by
    rw [card_eq_of_isZBasis hv hb, D.herm.finrank_eq]
    rfl
  set b := hex.choose_spec.choose
  let u : Fin hex.choose → EuclideanSpace ℂ (Ψ × Fin D.N) := fun k => D.hodgeFrame z (D.embHom (b k))
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  have hu_li : LinearIndependent ℝ u :=
    (D.herm.linearIndependent_real hbQ).map' (D.hodgeFrame z)
      (LinearMap.ker_eq_bot.2 (D.hodgeFrame_injective hz))
  have hgram : Matrix.gram ℝ u = Matrix.of fun k l => D.hodgeInner z (b k) (b l) := by
    ext k l
    exact D.inner_hodgeFrame z _ _
  have hlam0 : 0 ≤ D.lam1 z :=
    Real.sInf_nonneg (by rintro x ⟨w, -, -, rfl⟩; exact Real.sqrt_nonneg _)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range u), x ≠ 0 → D.lam1 z ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : ∑ k, c k • u k = D.hodgeFrame z (D.embHom (∑ k, c k • b k)) := by
      simp only [u, map_sum, map_zsmul]
    have hwI : ∑ k, c k • b k ∈ I := (hb.2 _).2 ((Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩)
    have hw0 : ∑ k, c k • b k ≠ 0 := by
      intro h
      apply hx0
      rw [hw, h, map_zero, map_zero]
    rw [hw, norm_eq_sqrt_real_inner, D.inner_hodgeFrame, D.hodgeInner_self]
    exact D.firstMinimum_le_period_norm z (hI hwI) hw0
  have key := pow_le_sqrt_det_gram u hu_li hlam0 hmin
  rw [hgram, ← hcov, hm] at key
  push_cast at key
  exact key

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Imports
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

theorem UnitaryFirstMinimumPositive.proof : UnitaryFirstMinimumPositive.Statement :=
  fun D => FirstMinPos.proof D

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsAlt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

theorem UnitaryIsotropicRank.proof : UnitaryIsotropicRank.Statement := by
  intro Em _ _ _ Ψ _ N j A I hI ρ v hv
  obtain ⟨-, hvI, hli, -⟩ := hv
  have hliE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).mp hli
  have hS : ∀ x ∈ (I : Set (Fin N → Em)), ∀ y ∈ (I : Set (Fin N → Em)), hermForm Em A.H x y = 0 := hI
  have hle : Submodule.span Em (Set.range v) ≤ Submodule.span Em (I : Set (Fin N → Em)) :=
    Submodule.span_mono (Set.range_subset_iff.2 hvI)
  calc ρ = Module.finrank Em (Submodule.span Em (Set.range v)) := by
        rw [finrank_span_eq_card hliE, Fintype.card_fin]
    _ ≤ Module.finrank Em (Submodule.span Em (I : Set (Fin N → Em))) := Submodule.finrank_mono hle
    _ ≤ N - j := IsotropicRank.proof Em Ψ N j A (I : Set (Fin N → Em)) hS

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PTorusIndex
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

theorem fg_of_isNzFamily {Em : Type} [Field Em] [NumberField Em] {N : ℕ} {I : Submodule (𝓞 Em) (Fin N → Em)}
    {ρ : ℕ} {v : Fin ρ → Fin N → Em} (hv : IsNzFamily I ρ v) : I.FG := by
  set J := Submodule.span (𝓞 Em) (Set.range v) with hJdef
  have hJ : J.FG := Submodule.fg_span (Set.finite_range v)
  set m := J.toAddSubgroup.relIndex I.toAddSubgroup with hmdef
  have hm : m ≠ 0 := hv.2.2.2
  have hmem : ∀ u ∈ I, m • u ∈ J := by
    intro u hu
    have h := AddSubgroup.nsmul_index_mem (J.toAddSubgroup.addSubgroupOf I.toAddSubgroup) ⟨u, hu⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    exact h
  have : IsNoetherian (𝓞 Em) J := isNoetherian_of_fg_of_noetherian J hJ
  let f : I →ₗ[𝓞 Em] J :=
    { toFun := fun u => ⟨m • (u : Fin N → Em), hmem u u.2⟩
      map_add' := fun a b => by ext1; simp [smul_add]
      map_smul' := fun c a => by ext1; simp [smul_comm] }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : m • (a : Fin N → Em) = m • (b : Fin N → Em) := congrArg Subtype.val hab
    rw [← Nat.cast_smul_eq_nsmul Em, ← Nat.cast_smul_eq_nsmul Em] at h1
    exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hm) h1)
  exact (Submodule.fg_top I).1 (fg_of_injective (N := ⊤) f hf)

theorem TorusIndex.proof (hA : EigenLatDifferent.Statement) (hB : DifferentLatIndex.Statement) :
    TorusIndex.Statement := by
  intro Em _ _ K _ _ ι hι N I ρ v hv s
  rw [hA Em K ι hι N I (fg_of_isNzFamily hv) s]
  exact hB Em K N I ρ v hv s

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUSemipositive
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def MUSemipositive.Statement (D : FullerData II Ψ K ι Ω E Em) {M : XModel D.toComponentData}
    (S : BoundedRegularisationSetting M D.Xo D.mu.aMu (HtBoundary.cuspWt D)) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (MUc D.mu S B p q t')

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.UnitaryCovolumeLowerBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

def UnitaryCovolumeLowerBound.Statement : Prop :=
  ∀ {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] (D : FullerData II Ψ K ι Ω E Em),
    ULamOne.Statement D

theorem UnitaryCovolumeLowerBound.neg_log_le {f ρ j' : ℕ} {lam rd nz c : ℝ} (hlam : 0 < lam) (hrd : 1 ≤ rd) (hρ : 1 ≤ ρ)
    (hρj : ρ ≤ j') (hc : c = nz * rd ^ (f * ρ)) (hmin : (lam / Real.sqrt (2 * f * ρ)) ^ (2 * f * ρ) ≤ c) :
    -Real.log nz ≤ (f * j' : ℝ) * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp only [mul_zero, zero_mul, pow_zero, mul_one, Nat.cast_zero] at hmin hc ⊢
    subst hc
    linarith [Real.log_nonneg hmin]
  have hF : (0 : ℝ) < f := by exact_mod_cast hf
  have hR : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hJ : (ρ : ℝ) ≤ j' := by exact_mod_cast hρj
  have hrd0 : 0 < rd := by linarith
  have hm : (0 : ℝ) < 2 * f * ρ := by positivity
  have hA : 0 < (lam / Real.sqrt (2 * f * ρ)) ^ (2 * f * ρ) := by positivity
  have hpow : 0 < rd ^ (f * ρ) := by positivity
  have hnz : 0 < nz := by
    by_contra hn
    push Not at hn
    have := mul_le_mul_of_nonneg_right hn hpow.le
    rw [zero_mul, ← hc] at this
    linarith
  have hlog := Real.log_le_log hA (hmin.trans_eq hc)
  rw [Real.log_pow, Real.log_div hlam.ne' (Real.sqrt_pos.2 hm).ne', Real.log_sqrt hm.le,
    Real.log_mul hnz.ne' hpow.ne', Real.log_pow] at hlog
  push_cast at hlog
  have h1 : -Real.log lam ≤ Real.posLog (1 / lam) := by
    have : Real.posLog (1 / lam) = max 0 (Real.log (1 / lam)) := rfl
    rw [this, one_div, Real.log_inv]
    exact le_max_right _ _
  have h2 : Real.log (2 * f * ρ) + Real.log rd ≤ Real.log (2 * f * j' * rd) := by
    rw [← Real.log_mul hm.ne' hrd0.ne']
    refine Real.log_le_log (by positivity) ?_
    gcongr
  have h3 : 0 ≤ 2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd) := by
    have hJ1 : (1 : ℝ) ≤ j' := by linarith [(by exact_mod_cast hρ : (1 : ℝ) ≤ ρ)]
    have hF1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have h4 : (1 : ℝ) ≤ 2 * f * j' := by
      have := one_le_mul_of_one_le_of_one_le hF1 hJ1
      linarith
    have : (1 : ℝ) ≤ 2 * f * j' * rd := one_le_mul_of_one_le_of_one_le h4 hrd
    linarith [Real.posLog_nonneg (x := 1 / lam), Real.log_nonneg this]
  have e1 : -Real.log nz ≤ f * ρ * (2 * -Real.log lam + (Real.log (2 * f * ρ) + Real.log rd)) := by
    linear_combination hlog
  have e2 : (f : ℝ) * ρ * (2 * -Real.log lam + (Real.log (2 * f * ρ) + Real.log rd)) ≤
      f * ρ * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e3 : (f : ℝ) * ρ * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) ≤
      f * j' * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ hF.le) h3
  linarith

theorem UnitaryCovolumeLowerBound.proof (hE : UnitaryCovolume.Statement) (hM : UnitaryMinkowskiBound.Statement) (hR : UnitaryIsotropicRank.Statement)
    (hP : UnitaryFirstMinimumPositive.Statement) : UnitaryCovolumeLowerBound.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D z hz
  have hlam := hP D z hz
  have hrd := UnitaryCovolumeLowerBound.one_le_rootDiscr Em
  have hcast : ((Fintype.card Ψ * (D.N - D.j) : ℕ) : ℝ) = (D.f * D.j' : ℝ) := by
    push_cast
    rfl
  rw [hcast, ← one_div]
  have hrhs : 0 ≤ (D.f * D.j' : ℝ) *
      (2 * Real.posLog (1 / D.lam1 z) + Real.log (2 * (D.f * D.j' : ℝ) * rootDiscr Em)) := by
    rcases Nat.eq_zero_or_pos (D.f * D.j') with h0 | h0
    · have : (D.f * D.j' : ℝ) = 0 := by exact_mod_cast h0
      rw [this, zero_mul]
    · have h1 : (1 : ℝ) ≤ D.f * D.j' := by exact_mod_cast h0
      have : (1 : ℝ) ≤ 2 * (D.f * D.j' : ℝ) * rootDiscr Em := by
        have h2 : (1 : ℝ) ≤ 2 * (D.f * D.j' : ℝ) := by linarith
        exact one_le_mul_of_one_le_of_one_le h2 hrd
      have := Real.log_nonneg this
      have := Real.posLog_nonneg (x := 1 / D.lam1 z)
      positivity
  unfold FullerData.cuspU
  refine max_le hrhs (Real.iSup_le (fun s => ?_) hrhs)
  by_cases h : ∃ ρ v, IsNzFamily (D.torLat s) ρ v
  · obtain ⟨ρ, v, hv⟩ := h
    rw [← mul_assoc 2]
    exact UnitaryCovolumeLowerBound.neg_log_le hlam hrd hv.1 (hR D.herm (D.torLat s) (D.torLat_iso s) ρ v hv)
      (hE D z hz (D.torLat s) (D.torLat_le s) (D.torLat_iso s) (D.torLat_sat s) ρ v hv)
      (hM D z hz (D.torLat s) (D.torLat_le s) ρ v hv)
  · have : D.nz z (D.torLat s) = 1 := by
      unfold FullerData.nz HermDatum.nz
      rw [dif_neg h]
    rw [this, Real.log_one, neg_zero]
    exact hrhs

end GroundTheory.Heights₂.Heights.NineStatements
end
end

