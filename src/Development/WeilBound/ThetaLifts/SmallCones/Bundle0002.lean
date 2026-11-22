import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.WeilBound.ThetaLifts.SmallCones.ColsOfMul
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0003

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ExpSum
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem summable_lat_wt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sz {κ : Type} [Fintype κ] (y : κ → AF F) : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j))

theorem norm_le_sz {κ : Type} [Fintype κ] (y : κ → AF F) : 1 + ‖fun j => evI F (y j)‖ ≤ sz y := by
  have h0 : ∀ j, 0 ≤ ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j)) := fun j =>
    Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
  refine add_le_add_right ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => h0 j)).2 fun j => ?_) 1
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j))
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (y j)))
    (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)

theorem sz_pos {κ : Type} [Fintype κ] (y : κ → AF F) : 0 < sz y := lt_of_lt_of_le (by positivity) (norm_le_sz y)

theorem summable_wt {κ : Type} [Fintype κ] {C : Set (κ → Af F)} (hC : IsCompact C) : ∃ N : ℕ, Summable fun ξ : κ → F =>
    if (fun j => (algebraMap F (AF F) (ξ j)).2) ∈ C then (sz (fun j => algebraMap F (AF F) (ξ j)) ^ N)⁻¹ else 0 := by
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hC
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, ?_⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine if_neg fun h0 => hξ ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ h0 i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_)
      ((summable_lat_wt (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj)
    · simp only [Function.comp_apply]
      split_ifs
      · exact inv_nonneg.2 (pow_pos (sz_pos _) _).le
      · exact le_rfl
    · simp only [Function.comp_apply]
      split_ifs
      · rw [inv_pow]
        refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ _)
        have h := norm_le_sz (fun i => algebraMap F (AF F) (ξ.1 i))
        have e : (fun i => evI F (algebraMap F (AF F) (ξ.1 i))) = fun i => mixedEmbedding F (ξ.1 i) :=
          funext fun i => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
        rw [e] at h
        exact h
      · positivity

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem slice_bound (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) :
    ∃ (wt : (Fin m → F) → ℝ) (P : SInf F (Fin n × Fin d) → ℝ), Summable wt ∧ Continuous P ∧ P 0 = 0 ∧
      ∀ y (f : SInf F (Fin n × Fin d)),
        ‖l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) (pureA F f φ)))‖ ≤ P f * wt y := by
  obtain ⟨r, φ₁, C, A, h1, hC, -, h2, h3, h4⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
  obtain ⟨N, hN⟩ := summable_wt hC
  choose T hT using fun i => hl (φ₁ i) (h1 i)
  choose p hp hq using fun i => h4 ((normSeminorm ℂ ℂ).comp (T i).toLinearMap) N (T i).continuous.norm
  refine ⟨_, fun f => ∑ i, p i f, hN, continuous_finset_sum _ fun i _ => hp i, by simp, fun y f => ?_⟩
  rw [h2, map_sum]
  simp only [hT]
  split_ifs with hy
  · rw [Finset.sum_mul]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _)]
    exact hq i i _ f
  · simp [h3 _ _ hy]

end PositivityTheory.ThKCT
end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def StabDec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → H.IsAdapted σ B Y Y₁ i₀ i₁ →
    (∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧ (p ∈ ratU σ Y.J → g₁ ∈ ratU σ Y₁.J)) ∧
    (∀ (ξ : Eˣ), ∀ g₁ ∈ ratU σ Y₁.J, ∀ m, IsLevi H (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁ m → m ∈ ratU σ Y.J) ∧
    ∀ t (g₁ : UA σ Y₁.J) m, IsLevi H t g₁ m → ∀ u ∈ unip σ Y H, m⁻¹ * u * m ∈ unip σ Y H

def ConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ z : ℕ, 2 * n = d + 2 * z ∧ min r s + 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ schA F (Fin n × Fin d), KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftA H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ)) h₁

def ConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoB H H') e → ∀ z : ℕ, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ M.So B.ψ B.τ₁, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftB σ H H') χW z (om (1, h) Φ)) h₁

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.IntegrableProdOfBound
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem integrable_prod_of_bound {G N : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] (μ : Measure G) [SFinite μ] (ν : Measure N) [IsFiniteMeasure ν]
    {f : G × N → ℂ} (hf : Continuous f) {K : ℝ} (hK : ∀ u, ∫⁻ g, ‖f (g, u)‖ₑ ∂μ ≤ ENNReal.ofReal K) : Integrable f (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hf.enorm.measurable.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono hK) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem ctFub_of (hU : UnipEx) (hT : ThetaBasic) (hG : GrpTop) (hE : EpsOf) : CTFub := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ ⟨C, k, hb⟩ c hc
  obtain ⟨⟨ν₀, 𝓕₀, a1, a2, a3⟩, ⟨Ω, hΩ, hcov⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH
  obtain ⟨b1, b2, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  obtain ⟨-, -, -, -, -, -, -, b3⟩ := hG F E σ hp.base.cm d W.J (hE F E σ B hp.base d W r' s' (Or.inr hp.skew)).1
  obtain ⟨t1, t2, -⟩ := (hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := hp.good.haar
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  have key : ∀ (ν : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), ν 𝓕 = 1 → ∀ h, SFinite (ν.restrict 𝓕) ∧
      Integrable (fun x : UA σ X.J × unip σ W H' => theta om Φ x.1 (x.2.1 * h)) ((M.μ.restrict M.dom).prod (ν.restrict 𝓕)) := by
    intro ν 𝓕 h1 h
    have hf : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
    have hcont : Continuous fun u : unip σ W H' => u.1 * h := continuous_subtype_val.mul continuous_const
    obtain ⟨D, hD⟩ := b3 _ (hΩ.image hcont)
    refine ⟨@instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite _), integrable_prod_of_bound _ _ (K := |C| * (D : ℝ) ^ k)
      (t1.comp (continuous_fst.prodMk (hcont.comp continuous_snd))) fun u => ?_⟩
    obtain ⟨γ, hγ, hu⟩ := hcov u
    have e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u).1 * h) := fun g => by
      rw [← t2 1 (one_mem _) γ.1 hγ g, one_mul, Subgroup.coe_mul, mul_assoc]
    simp only [e]
    refine (hb _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (ht ((γ * u).1 * h) : ℝ) ≤ D := hD _ ⟨_, hu, rfl⟩
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 k) (by positivity) (abs_nonneg C)
  refine ⟨fun h => ?_, fun ν 𝓕 c1 c2 c3 h => ?_⟩
  · obtain ⟨_, hi⟩ := key ν₀ 𝓕₀ a3 h
    simp only [fun g => hc g ν₀ 𝓕₀ a1 a2 a3 h]
    exact hi.integral_prod_left
  · obtain ⟨_, hi⟩ := key ν 𝓕 c3 h
    simp only [fun g => hc g ν 𝓕 c1 c2 c3 h]
    exact integral_integral_swap (f := fun (g : UA σ X.J) (u : unip σ W H') => theta om Φ g (u.1 * h)) hi

end PositivityTheory.ThKCT
end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.MatCancel
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Fr

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKG.Tow.Levi (sig_sig cA_cA exists_UA)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_det {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := fun hm => by
  obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hm
  have := h.2.2 (star x) (by simpa using hx)
  rw [star_star, e, dotProduct_zero] at this
  exact lt_irrefl _ this

variable {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

theorem det_ne (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
  rcases hY with h | h
  · intro h0
    refine cartan_det (h.cartan u) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · exact PositivityTheory.ThKG.Tow.Levi.det_ne_zero h

theorem exists_eps (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) :
    ∃ ε : ℤˣ, (∀ i j, σ (Y.J j i) = ((ε : ℤ) : E) * Y.J i j) ∧ Y.L.IsLattice E := by
  rcases hY with h | h
  · exact ⟨1, fun i j => by simp [h.herm], h.lat⟩
  · exact ⟨-1, fun i j => by simp [h.skew], h.lat⟩

theorem form_eps (hs : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (x y : Fin n → E) :
    σ (form σ J y x) = ((ε : ℤ) : E) * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, hs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hJ]; ring

theorem eps_sq (ε : ℤˣ) : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem isFr (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    ∃ (ε : E) (A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E), IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A' := by
  obtain ⟨ε, hε, hL⟩ := exists_eps hY
  have hsk : ∀ x y, form σ Y.J x y = ((ε : ℤ) : E) * σ (form σ Y.J y x) := fun x y => by
    rw [form_eps (sig_sig hB.cm) hε, ← mul_assoc, eps_sq, one_mul]
  have ent : ∀ a b, ((fr H.ι H.x H.y)ᵀ * Y.J * (fr H.ι H.x H.y).map (σ : E →+* E)) a b =
      form σ Y.J (fun i => fr H.ι H.x H.y i a) (fun i => fr H.ι H.x H.y i b) := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have col : ∀ j, (fun i => fr H.ι H.x H.y i (Sum.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    ext i; simp [fr]
  have hs : ∀ z : Fin n → E, z ∈ LinearMap.range (Matrix.toLin' (fr H.ι H.x H.y)) := fun z => by
    have hz : z ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
    refine (Submodule.span_le.2 fun z hz => ?_) hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    exact ⟨Sum.elim u ![s, t], by rw [Matrix.toLin'_apply, fr_mulVec]; abel⟩
  choose f hf using fun j => hs (Pi.single j 1)
  have h1 : fr H.ι H.x H.y * (Matrix.of fun a j => f j a) = 1 := by
    ext i j
    rw [Matrix.one_apply, ← Pi.single_apply, ← hf j]; rfl
  refine ⟨(ε : ℤ), _, eps_sq ε, ?_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h1⟩
  ext (a | a) (b | b)
  · exact congrFun (congrFun hH.gram a) b
  · rw [ent, col]
    fin_cases b
    exacts [(hH.orth _).1, (hH.orth _).2]
  · rw [ent, col, hsk]
    fin_cases a
    · exact (congrArg (fun z => _ * σ z) (hH.orth _).1).trans (by simp [gr])
    · exact (congrArg (fun z => _ * σ z) (hH.orth _).2).trans (by simp [gr])
  · rw [ent]
    fin_cases a <;> fin_cases b
    exacts [hH.xx, hH.xy, (hsk _ _).trans ((congrArg (fun z => _ * σ z) hH.xy).trans (by simp [gr])), hH.yy]

variable {ε : E} {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E}

theorem IsFr.ad (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') :
    IsFr (cA σ : AE F E →+* AE F E) (inclR (F := F) (AF F) ε) (incM F Y.J) (incM F Y₁.J) (incM F H.ι) (incV F H.x) (incV F H.y)
      (incM F A') :=
  h.map (inclR (F := F) (AF F)) fun _ => rfl

theorem mat_mul {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inj {J : Matrix (Fin n) (Fin n) E} {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_cancel {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z : Fin n → AE F E) : mat g⁻¹ *ᵥ (mat g *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]

theorem mat_cancel' {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z : Fin n → AE F E) : mat g *ᵥ (mat g⁻¹ *ᵥ z) = z := by
  simpa using mat_cancel g⁻¹ z

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F ⊗[F] E) := by
    haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    infer_instance
  (inclR (F := F) (E := E) (AF F)).injective

theorem mem_ratU {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} : g ∈ ratU σ J ↔ ∃ M, mat g = incM F M := by
  refine ⟨fun h => ?_, fun ⟨M, hM⟩ => ?_⟩
  · obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 h
    exact ⟨u.1, (congrArg Units.val hu).symm⟩
  · haveI : Nontrivial (AE F E) := inclR_inj.nontrivial
    have h1 : IsUnit (mat g).det := (Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit
    have h2 : M.det ≠ 0 := fun h0 => by
      rw [hM, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
      exact not_isUnit_zero h1
    exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M h2, Units.ext hM.symm⟩

theorem mem_unip {u : UA σ Y.J} : u ∈ unip σ Y H ↔ mat u *ᵥ incV F H.x = incV F H.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨Matrix.one_mulVec _, fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  | mul a b _ _ ha hb =>
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hb.1, ha.1], fun z => ?_⟩
    obtain ⟨s, hs⟩ := ha.2 z
    obtain ⟨t, ht⟩ := hb.2 z
    exact ⟨s + t, by rw [mat_mul, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_add, hs, Matrix.mulVec_smul, ha.1, add_smul, add_assoc]⟩
  | inv a _ ha =>
    have e : mat a⁻¹ *ᵥ incV F H.x = incV F H.x := by conv_lhs => rw [← ha.1, mat_cancel]
    refine ⟨e, fun z => ?_⟩
    obtain ⟨s, hs⟩ := ha.2 z
    have := mat_cancel a (incM F H.ι *ᵥ z)
    rw [hs, Matrix.mulVec_add, Matrix.mulVec_smul, e] at this
    exact ⟨-s, by rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]⟩

theorem exists_levi (hσ : IsCMExt F E σ) (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') (t : (AE F E)ˣ) (g : UA σ Y₁.J) :
    ∃ m : UA σ Y.J, IsLevi H t g m ∧
      mat m = fr (incM F H.ι) (incV F H.x) (incV F H.y) * dg (mat g) t.1 (cA σ (t⁻¹).1) * incM F A' := by
  obtain ⟨m, m', e0, e1, e2, e3, e4, e5⟩ := h.ad.levi (cA_cA hσ) t.mul_inv g.1.mul_inv g.2
  obtain ⟨p, rfl⟩ := exists_UA e1 e2
  exact ⟨p, ⟨e3, e4, e5⟩, e0⟩

theorem levi_uniq (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m m' : UA σ Y.J}
    (h1 : IsLevi H t g m) (h2 : IsLevi H t g m') : m = m' :=
  mat_inj (h.ad.ext (h1.1.trans h2.1.symm) (h1.2.1.trans h2.2.1.symm) (h1.2.2.trans h2.2.2.symm))

theorem levi_mul {t t' : (AE F E)ˣ} {g g' : UA σ Y₁.J} {m m' : UA σ Y.J} (h1 : IsLevi H t g m) (h2 : IsLevi H t' g' m') :
    IsLevi H (t * t') (g * g') (m * m') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.1, Matrix.mulVec_smul, h1.1, smul_smul, Units.val_mul, mul_comm]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.2.1, Matrix.mulVec_smul, h1.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [mat_mul, Matrix.mul_assoc, h2.2.2, ← Matrix.mul_assoc, h1.2.2, Matrix.mul_assoc, mat_mul]

theorem levi_one : IsLevi (W := Y) (W₁ := Y₁) (σ := σ) H 1 1 1 :=
  ⟨by simp [mat_one], by simp [mat_one], by simp [mat_one]⟩

theorem levi_inv {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) : IsLevi H t⁻¹ g⁻¹ m⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · have := mat_cancel m (incV F H.x)
    rw [h1.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, Units.inv_mul, one_smul]
  · have := mat_cancel m (incV F H.y)
    rw [h1.2.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, ← map_mul, inv_inv, Units.mul_inv, map_one, one_smul]
  · have : mat m⁻¹ * (incM F H.ι * mat g) = incM F H.ι := by
      rw [← h1.2.2, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    conv_rhs => rw [← this, Matrix.mul_assoc, Matrix.mul_assoc, ← mat_mul, mul_inv_cancel, mat_one, Matrix.mul_one]

theorem levi_vec {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) (z : Fin n₁ → AE F E) :
    mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, h1.2.2, Matrix.mulVec_mulVec]

theorem levi_conj {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) {u : UA σ Y.J} (hu : u ∈ unip σ Y H) :
    m⁻¹ * u * m ∈ unip σ Y H := by
  obtain ⟨a, b⟩ := mem_unip.1 hu
  have h2 := levi_inv h1
  refine mem_unip.2 ⟨?_, fun z => ?_⟩
  · rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1.1, Matrix.mulVec_smul, a, ← h1.1, mat_cancel]
  · obtain ⟨c, hc⟩ := b (mat g *ᵥ z)
    exact ⟨c * (t⁻¹).1, by rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, levi_vec h1, hc,
      Matrix.mulVec_add, levi_vec h2, mat_cancel, Matrix.mulVec_smul, h2.1, smul_smul]⟩

theorem stab_dec (hσ : IsCMExt F E σ) (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') (hd : Y.J.det ≠ 0) (p : UA σ Y.J)
    (t : (AE F E)ˣ) (hp : mat p *ᵥ incV F H.x = t.1 • incV F H.x) :
    ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧
      mat g₁ = (incM F A' * mat p * fr (incM F H.ι) (incV F H.x) (incV F H.y)).toBlocks₁₁ := by
  obtain ⟨g, α, e0, hg, hα⟩ := h.ad.stab t.mul_inv p.2 hp
  have hgu : IsUnit g.det := by
    have e := congrArg Matrix.det hg
    have hd' : IsUnit (incM F Y₁.J).det := by
      have := (h.isUnit_det hd.isUnit).map (inclR (F := F) (AF F))
      rwa [RingHom.map_det] at this
    rw [← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd'
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd')
  obtain ⟨g₁, rfl⟩ := exists_UA (σ := σ) (Matrix.mul_nonsing_inv _ hgu) hg
  obtain ⟨m, hm, -⟩ := exists_levi hσ h t g₁
  have h2 := levi_inv hm
  refine ⟨p * m⁻¹, mem_unip.2 ⟨?_, fun z => ⟨α ⬝ᵥ (mat g₁⁻¹ *ᵥ z), ?_⟩⟩, g₁, m, hm, by group, e0⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.1, Matrix.mulVec_smul, hp, smul_smul, Units.inv_mul, one_smul]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, levi_vec h2]
    exact (hα _).trans (by rw [mat_cancel'])

end PositivityTheory.ThKCT.Fr

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SoDefs
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def LinEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW t) = 0 → evFin F v (sy σ X W x u) =
        ((X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ)ᵀ * u.map (piW t)).trace

def SoZeroA' : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₀.IsGood B.ψ → ∀ M₁ : Model σ X W₁, M₁.IsGood B.ψ →
    (∃ χX χW om₁ om₀ r₁ s₁ r₀ s₀ r₂ s₂, IsPair B M₁ χX χW om₁ r₁ s₁ r₂ s₂ ∧ IsPair B M₀ χX χW om₀ r₀ s₀ r₂ s₂) →
    ∀ e₀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ Ψ ∈ schA F _,
      e₀ Ψ ∈ M₁.So B.ψ B.τ₁ → e Ψ = 0

end PositivityTheory.ThKCT

end
end

