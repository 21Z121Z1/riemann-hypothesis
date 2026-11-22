import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceExpSmulStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absDetOnStableSubspace_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)), (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ, GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  first | exact @GlobalTheory.FlagMeas.detOn_exp_smul | exact GlobalTheory.FlagMeas.detOn_exp_smul | (intros; apply GlobalTheory.FlagMeas.detOn_exp_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockDetSingleBlockSecondEqOneOfLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mem_blockTriangular_singleBlock_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ Formalism.L2.DIV.blockTri (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) := by
  rw [Formalism.L2.DIV.mem_blockTri]
  intro i j hij
  have hi : Formalism.L2.DIV.blk2 r i = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le i.isLt h)
  have hj : Formalism.L2.DIV.blk2 r j = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le j.isLt h)
  rw [hi, hj] at hij
  exact absurd hij (lt_irrefl 0)

theorem blockDet_singleBlock_second_eq_one_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.dBlk (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) 1 g = 1 := by
  have hm := mem_blockTriangular_singleBlock_of_le (κ := κ) h g
  haveI : IsEmpty {a : Fin n // Formalism.L2.DIV.blk2 r a = 1} := by
    refine ⟨fun a => ?_⟩
    have h1 := a.2
    have h2 := a.1.isLt
    unfold Formalism.L2.DIV.blk2 at h1
    split_ifs at h1 with hlt <;> omega
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hm, Units.val_one]
  exact Matrix.det_isEmpty

theorem levG_twist_trivial_of_rank_eq :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank), V.rank = r → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) = levG V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) ∧ ∀ k ∈ levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B), levChi V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) k = levChi V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) k := by
  intro D V β r t hr hrk Pg Q P χ ξ
  subst hrk
  have hlev : Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) =
      Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) := by
    ext x
    simp only [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    constructor
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      refine ⟨⟨h1, h2, h3, fun PP hPP => ?_⟩, h5⟩
      change PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) at hPP
      simp at hPP
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      exact ⟨⟨h1, h2, h3, fun PP _ => mem_blockTriangular_singleBlock_of_le (r := V.rank) le_rfl _⟩, h5⟩
  have hfn : ∀ y, Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) y =
      Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) y := by
    intro y
    unfold Formalism.L2.DIV.levFn
    have hq : ∏ PP ∈ (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).Q,
        (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP
          (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).r) 1
            (Formalism.L2.DIV.redFn β PP y)) = 1 := by
      refine Finset.prod_eq_one fun PP _ => ?_
      have h2 := blockDet_singleBlock_second_eq_one_of_le (r := V.rank) (le_refl V.rank) (Formalism.L2.DIV.redFn β PP y)
      exact (congrArg (⇑((datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP)) h2).trans (map_one _)
    rw [hq]
    change _ = _ * ∏ PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)), _
    rw [Finset.prod_empty]
    rfl
  refine ⟨?_, fun k _ => ?_⟩
  · unfold levG
    rw [hlev]
  · unfold levChi
    rw [hfn]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseRangeFiniteVectorsDiscreteSeriesStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_range_finite_vectors_discrete_series : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T), Nontrivial D.HK.V → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → Dense (Set.range D.ι) := by
  first | exact @GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | exact GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | (intros; apply GlobalTheory.AnalyticDense.dense_range_of_factorial_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsThetaPOfIntegrable
section
open MeasureTheory Formalism.IndefR

namespace GlobalTheory.ThetaIntegralLinear

theorem exists_isThetaP_of_integrable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by

  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν)
    ?_ ?_ ?_ ?_, hint, ?_⟩
  · intro f₁ f₂ e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    exact integral_add (hint f₁ e g) (hint f₂ e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e₁ e₂
    funext g
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    exact integral_add (hint f e₁ g) (hint f e₂ g)
  · intro c f e
    funext g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e g
    rfl

end GlobalTheory.ThetaIntegralLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsometryIntertwinerOfDerivedActionStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_intertwiner_of_derived_action : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T) (πU : URep T) (E : D.HK.V →ₗ[ℂ] πU.H), Dense (Set.range D.ι) → (∀ y, ‖E y‖ = ‖D.ι y‖) → (∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E y)) (E (D.HK.act Y y)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ j : D.U.H →ₗᵢ[ℂ] πU.H, (∀ y, j (D.ι y) = E y) ∧ ∀ g x, j (D.U.π g x) = πU.π g (j x) := by
  first | exact @GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived | exact GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived | (intros; apply GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteRealPointsCommute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.FinRealComm

private theorem eq_map_inl_fst_add_map_inr_snd_tmul {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E) :
    z = TensorProduct.map (LinearMap.inl F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
        TensorProduct.map (LinearMap.inr F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.map_tmul, ← TensorProduct.add_tmul]
    congr 1
    ext <;> simp
  | add u v hu hv =>
    rw [map_add, map_add, map_add, map_add]
    conv_lhs => rw [hu, hv]
    abel

theorem tensor_prod_ext {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (x y : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  rw [eq_map_inl_fst_add_map_inr_snd_tmul x, eq_map_inl_fst_add_map_inr_snd_tmul y, h1, h2]

theorem GA_ext_inf_fin {D : D7} (V : HSp D) (x y : GA D V)
    (h1 : infHom V x = infHom V y) (h2 : finHom V x = finHom V y) : x = y := by
  have hm : (matHom V x).1 = (matHom V y).1 := by
    ext i j
    have e1 := congrArg (fun g => g.1 i j) h1
    have e2 := congrArg (fun g => g.1 i j) h2
    simp only [infHom, finHom, MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map,
      MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e1 e2
    exact tensor_prod_ext _ _ e1 e2
  exact Subtype.ext (Units.ext hm)

theorem finite_real_points_commute :
    ∀ {D : D7} (V : HSp D) (a b : GA D V), a ∈ GfC V → b ∈ GinfC V → a * b = b * a := by
  intro D V a b ha hb
  have ha' : infHom V a = 1 := ha
  have hb' : finHom V b = 1 := hb
  apply GA_ext_inf_fin V
  · rw [map_mul, map_mul, ha', one_mul, mul_one]
  · rw [map_mul, map_mul, hb', one_mul, mul_one]

end GlobalTheory.FinRealComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem fundamentalDomain_setIntegral_mul_right :
    ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ k : G, Measure.map (fun g => g * k) μ = μ → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ → IntegrableOn (fun g => f (g * k)) 𝓕 μ ∧ ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  intro G _ _ _ _ Γ _ μ _ 𝓕 h𝓕 k hk f hf hi
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h𝓕.integrableOn_iff h2 hinv]
    exact (hmp.integrableOn_comp_preimage hemb).2 hi
  · rw [h𝓕.setIntegral_eq h2 hinv]
    exact hmp.setIntegral_preimage_emb hemb f 𝓕

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasTypeOfMemMult
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem hasType_of_mem_mult : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), ∀ T ∈ Mult θ M (levG V β L : Set (GA D V)) (levChi V β L), ∀ v, HasType V β L (T v) := by
  intro D V S θ M β L T hT v
  induction hT using Submodule.span_induction generalizing v with
  | mem x hx => exact fun κ hκ h => hx.lev v κ hκ h
  | zero => intro κ _ h; simp
  | add x y _ _ hx hy =>
    intro κ hκ h
    simp only [MultilinearMap.add_apply, Pi.add_apply]
    rw [hx v κ hκ h, hy v κ hκ h, mul_add]
  | smul a x _ hx =>
    intro κ hκ h
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hx v κ hκ h, mul_left_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

variable {D : D7} (θ : InfFam D) (V : HSp D)

theorem comm_fin_real {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GinfC V) : a * b = b * a := by
  have h1 : (GfC V).Normal := MonoidHom.normal_ker _
  have h2 : (GinfC V).Normal := MonoidHom.normal_ker _
  exact Subgroup.commute_of_normal_of_disjoint (GfC V) (GinfC V) h1 h2
    (Subgroup.disjoint_def.2 fun {x} hx hy => GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hx hy) a b ha hb

theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V :=
  atTau_mem θ V τ _

def rTrL (κ : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := LinearMap.funLeft ℂ ℂ fun g => g * κ

theorem rTrL_apply (κ : GA D V) (φ : GA D V → ℂ) : rTrL V κ φ = rTr V κ φ := rfl

variable {κ : GA D V}

theorem Rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ φ) = rTr V κ (Rder θ V τ X φ) := by
  funext g
  simp only [Rder, rTr]
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, comm_fin_real V hκ (oneP_mem θ V τ X t)]

theorem RderC_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ Z (rTr V κ φ) = rTr V κ (RderC θ V τ Z φ) := by
  unfold RderC
  rw [Rder_rTr θ V hκ, Rder_rTr θ V hκ]
  rfl

theorem foldr_comm {α : Type} (T : α → α) (l : List (α → α)) (hl : ∀ f ∈ l, ∀ x, f (T x) = T (f x)) (x : α) :
    l.foldr (fun f acc => f acc) (T x) = T (l.foldr (fun f acc => f acc) x) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldr_cons]
    rw [ih fun g hg => hl g (List.mem_cons_of_mem _ hg), hl f List.mem_cons_self]

theorem gelf_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ k (rTr V κ φ) = rTr V κ (gelf θ V τ k φ) := by
  unfold gelf
  rw [← rTrL_apply V κ (∑ _, _), map_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [rTrL_apply]
  refine foldr_comm (rTr V κ) _ ?_ φ
  intro f hf x
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
  exact RderC_rTr θ V hκ τ _ x

theorem foldr_Rder_rTr (hκ : κ ∈ GfC V) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (rTr V κ φ) = rTr V κ (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih, Rder_rTr θ V hκ]

theorem isAutFun_rTr (hκ : κ ∈ GfC V) {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (rTr V κ φ) := by
  have := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const)⟩
  · simp only [rTr]
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, hinv⟩ := h.level
    refine ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have hc : Continuous fun k : GA D V => κ⁻¹ * k * κ⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hU.preimage hc
    · have hk' : κ⁻¹ * k * κ⁻¹⁻¹ ∈ U := hk
      have hf : κ⁻¹ * k * κ⁻¹⁻¹ ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hκ) hkf) ((GfC V).inv_mem ((GfC V).inv_mem hκ))
      simp only [rTr]
      rw [← hinv _ hk' hf (g * κ)]
      congr 1
      group

theorem isAutFunSm_rTr : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ,
    IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  intro D θ V κ hκ φ h
  refine ⟨isAutFun_rTr V hκ h.toIsAutFun, fun k τs Xs hX g => ?_, ?_, ?_⟩
  · have e : (fun t : Fin k → ℝ => rTr V κ φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) =
        fun t : Fin k → ℝ => φ (g * κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
      funext t
      have hm : (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V := by
        refine (GinfC V).list_prod_mem fun x hx => ?_
        obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
        exact oneP_mem θ V _ _ _
      simp only [rTr]
      rw [mul_assoc, mul_assoc, comm_fin_real V hκ hm]
    rw [e]
    exact h.smooth k τs Xs hX (g * κ)
  · obtain ⟨W, hW, hφ, hst⟩ := h.zfin
    refine ⟨W.map (rTrL V κ), inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨gelf θ V τ k f, hst τ k f hf, (gelf_rTr θ V hκ τ k f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * κ)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_rTr θ V hκ]
    simp only [rTr]
    rw [mul_assoc, ← comm_fin_real V hκ hg, ← mul_assoc]
    exact hC g hg

end GlobalTheory.FinTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  refine ⟨(GfC V).mul_mem hκ.1 hκ'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hκ.2.1 hκ'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ.2.1 hκ'.2.1, hκ.2.2, hκ'.2.2]

theorem levChi_flag_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ.2.1 hκ'.2.1, Units.val_mul]

theorem levChi_flag1 (κ : GA D V) : levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_flag1]

theorem isLift_one_of_mem {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  refine ⟨hκ.1, hκ.2.1, ?_⟩
  have h : Formalism.L2.DIV.rTup β L (finE V κ) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)) := hκ.2.2
  exact Subgroup.mem_bot.mp h

theorem act_one {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : actG0 V β L 1 F = F := by
  have h1 : (1 : GA D V) ∈ levG V β (flag1L L) := Subgroup.one_mem _
  have hl := isLift_one_of_mem h1
  funext h
  rw [level_action_spec hF ⟨1, hl⟩ 1 hl h, hF 1 h1 h, levChi_flag1]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) 1
  field_simp

theorem act_hasType {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) : HasType V β (flag1L L) (actG0 V β L g F) := by
  intro k hk h
  obtain ⟨κ, hκ⟩ := hex
  have hl := isLift_one_of_mem hk
  have hkκ : IsLevelLift V β L g (k * κ) := by simpa using isLift_mul hl hκ
  rw [level_action_spec hF ⟨κ, hκ⟩ κ hκ (h * k), level_action_spec hF ⟨κ, hκ⟩ (k * κ) hkκ h, levChi_flag_mul hl hκ,
    levChi_flag1, mul_assoc h k κ]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) k
  have := levChi_ne_zero (V := V) (β := β) (flagL L) κ
  field_simp

theorem act_mul {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g g' : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) (hex' : ∃ κ, IsLevelLift V β L g' κ) :
    actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  obtain ⟨κ, hκ⟩ := hex
  obtain ⟨κ', hκ'⟩ := hex'
  have hm := isLift_mul hκ hκ'
  funext h
  rw [level_action_spec hF ⟨_, hm⟩ _ hm h, level_action_spec (act_hasType hF ⟨κ', hκ'⟩) ⟨κ, hκ⟩ κ hκ h,
    level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (h * κ), levChi_flag_mul hκ hκ', mul_assoc h κ κ', mul_inv, mul_assoc]

theorem levelGroupAction_isAction : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), LiftsExist V β L → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (actG0 V β L 1 F = F ∧ ∀ g, HasType V β (flag1L L) (actG0 V β L g F)) ∧ ∀ g g', actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  intro D V β L hL F hF
  exact ⟨⟨act_one hF, fun g => act_hasType hF (hL g)⟩, fun g g' => act_mul hF (hL g) (hL g')⟩

end GlobalTheory.FlagAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mult_value_left_cont_level :
    ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ, ∀ T ∈ Mult θ M J χ, ∀ v, (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ Continuous (T v) ∧ ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro D V S θ M J χ T hT v
  induction hT using Submodule.span_induction with
  | mem x hx =>
    exact ⟨(hx.aut v).left, (hx.aut v).cont, hx.lev v⟩
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_, fun k _ g => ?_⟩
    · simp
    · simp only [MultilinearMap.zero_apply]
      exact continuous_zero
    · simp
  | add x y _ _ hx hy =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · simpa only [MultilinearMap.add_apply] using hx.2.1.add hy.2.1
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2.2 k hk g, hy.2.2 k hk g, mul_add]
  | smul c x _ hx =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 γ hγ g]
    · simpa only [MultilinearMap.smul_apply] using hx.2.1.const_smul c
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2.2 k hk g]
      ring

end GlobalTheory
end

