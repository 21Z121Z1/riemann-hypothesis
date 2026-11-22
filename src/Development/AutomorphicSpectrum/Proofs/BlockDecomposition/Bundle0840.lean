import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0834
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0831
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0832
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0830
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0824
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerOfFibIntEqZero
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem mem_twKer_of_sum {G X ι : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (N : Subgroup G) (T : Finset ι) (hT : T.Nonempty) (g : ι → N) (x : X) (hs : ∑ t ∈ T, ρ (g t : G) x = 0) :
    x ∈ twKer ρ N 1 := by
  have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
  have hmem : ∀ t ∈ T, x - ρ (g t : G) x ∈ twKer ρ N 1 := by
    intro t _
    have hg : ρ (g t : G) x - (((1 : N →* ℂˣ) (g t) : ℂˣ) : ℂ) • x ∈ twKer ρ N 1 :=
      Submodule.subset_span ⟨g t, x, rfl⟩
    have := (twKer ρ N 1).neg_mem hg
    simpa using this
  have hs' : (T.card : ℂ) • x = ∑ t ∈ T, (x - ρ (g t : G) x) := by
    rw [Finset.sum_sub_distrib, hs, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have h1 : (T.card : ℂ) • x ∈ twKer ρ N 1 := by
    rw [hs']
    exact Submodule.sum_mem _ hmem
  exact ((twKer ρ N 1).smul_mem_iff hc).1 h1

theorem exists_reps {L : Type} [Group L] (K : Subgroup L) (hK : K.FiniteIndex) :
    ∃ T : Finset L, T.Nonempty ∧ ∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K := by
  classical
  haveI : Fintype (L ⧸ K) := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset (L ⧸ K)).image Quotient.out, ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk 1))⟩, ?_⟩
  intro x
  refine ⟨(QuotientGroup.mk x : L ⧸ K).out, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
  · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  · rintro t ⟨ht, hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    have : q = (QuotientGroup.mk x : L ⧸ K) := by
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hx
    rw [this]

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_mulH {n : ℕ} (κ : GL (Fin n) k) : Continuous (mulH κ) := by
  have : Continuous fun y : Fin n → k => (κ : Matrix (Fin n) (Fin n) k).mulVec y :=
    Continuous.matrix_mulVec continuous_const continuous_id
  exact continuous_ofAdd.comp (this.comp continuous_toAdd)

theorem continuous_uMh (n : ℕ) : Continuous (uMh k n) :=
  (GlobalTheory.T.continuous_levi_unipotent_proj k n).2.1.comp continuous_toAdd

theorem exists_sum_eq_zero_abs (n : ℕ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) Y) (hρ : IsSmooth ρ)
    (ρ' : Representation ℂ (Multiplicative (Fin n → k)) X) (hρ' : IsSmooth ρ')
    (S : Set (GL (Fin n) k)) (hS : ∀ κ ∈ S, κ ∈ GlobalTheory.SplitWeil.KO k (Fin n))
    (F : GL (Fin n) k → X →ₗ[ℂ] Y)
    (hF : ∀ κ ∈ S, ∀ y x, F κ (ρ' y x) = ρ (mulH κ y) (F κ x))
    (hinj : ∀ x, (∀ κ ∈ S, F κ x = 0) → x = 0)
    (x : X) (hx : ∀ κ ∈ S, F κ x ∈ twKer ρ ⊤ 1) (hfin : ((fun κ => F κ x) '' S).Finite) :
    ∃ T : Finset (Multiplicative (Fin n → k)), T.Nonempty ∧ ∑ y ∈ T, ρ' y x = 0 := by
  classical
  obtain ⟨c, hc, hS'⟩ := GlobalTheory.T.finite_jacquet_kernel_common_lattice k n ρ _ hfin (by
    rintro _ ⟨κ, hκ, rfl⟩
    exact hx κ hκ)
  have hcomp : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := isCompact_Lc n hc
  have hθ : IsOpen (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) := by
    have : (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) = Set.univ := by
      ext l
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isOpen_univ
  set K := GlobalTheory.CompanionTheory.TwistedAverage.stabKer ρ' (Lc n c) 1 x with hK
  have hKo : IsOpen (K : Set (Lc n c)) := GlobalTheory.CompanionTheory.TwistedAverage.isOpen_stabKer hρ' _ _ hθ x
  have hKf : K.FiniteIndex := GlobalTheory.CompanionTheory.TwistedAverage.finiteIndex_stabKer hρ' hcomp _ hθ x
  obtain ⟨T, hTn, hT⟩ := exists_reps K hKf
  refine ⟨T.image Subtype.val, hTn.image _, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  refine hinj _ fun κ hκ => ?_
  rw [map_sum]
  have hsmooth : IsSmooth (MonoidHom.comp ρ (mulH κ)) := fun v =>
    (hρ v).preimage (continuous_mulH κ)
  have key := GlobalTheory.T.sum_over_compact_cosets_jacquet_kernel (MonoidHom.comp ρ (mulH κ)) hsmooth (Lc n c) hcomp (F κ x)
    (GlobalTheory.T.jacquet_kernel_lattice_conj_compact k n ρ c κ (hS κ hκ) _ (hS' _ ⟨κ, hκ, rfl⟩)) K T hKo
    (fun l hl => by
      have h1 : ρ' (l : Multiplicative (Fin n → k)) x = x := hl.1
      have h2 := hF κ hκ (l : Multiplicative (Fin n → k)) x
      rw [h1] at h2
      exact h2.symm) hT
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  exact hF κ hκ _ x

theorem mem_twKer_fibAct (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (φ : fibM (Fin t → k) Z) (h : smInt μ φ.1 ∈ twKer ρ₀ ⊤ 1) : φ ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  classical
  obtain ⟨c, hc, hinv⟩ := GlobalTheory.T.exists_lattice_periodicity k t φ.1 φ.2.1 φ.2.2
  obtain ⟨A, hA⟩ := GlobalTheory.T.locally_constant_coset_indicator_sum k t φ.1 c hc φ.2.2 hinv
  have hφ : φ.1 = fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ.1 a) v := funext hA
  have hsum : φ = ∑ a ∈ A, cosetFn t hc a (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [hA v, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hI := GlobalTheory.T.integral_coset_indicator_sum k t μ c hc A φ.1
  rw [← hφ] at hI
  rw [hI] at h
  have hz : ∑ a ∈ A, φ.1 a ∈ twKer ρ₀ ⊤ 1 := ((twKer ρ₀ ⊤ 1).smul_mem_iff (GlobalTheory.T.haar_measure_coset_ne_zero k t μ c hc)).1 h
  have h0 : cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, cosetFn t hc 0 (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [Submodule.coe_sum, Finset.sum_apply]
    have e : ∀ z : Z, (cosetFn t hc 0 z).1 v = (cosetSet t c 0).indicator (fun _ => z) v := fun _ => rfl
    simp only [e]
    by_cases hv : v ∈ cosetSet t c 0
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv, Finset.sum_const_zero]
  have hd : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    have e : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, (cosetFn t hc a (φ.1 a) - cosetFn t hc 0 (φ.1 a)) := by
      rw [h0, Finset.sum_sub_distrib, ← hsum]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => GlobalTheory.T.coset_function_translate_jacquet_kernel k i t ρ₀ c hc a _
  have := (twKer (fibAct t ρ₀) ⊤ 1).add_mem hd (GlobalTheory.T.coset_function_jacquet_kernel k i t ρ₀ c hc _ hz)
  simpa using this

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    (κ : GL (Fin (i + t)) k) : cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] fibM (Fin t → k) (V ⊗[ℂ] W) :=
  LinearMap.codRestrict (fibM (Fin t → k) (V ⊗[ℂ] W))
    (LinearMap.pi fun v => evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) κ))
    (fun x => GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ x κ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_of_fibInt_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ f : cIndSpace (HPG k i t) (hRep τ σ), (∀ g, fibInt μ f g = 0) → f ∈ twKer (prodPG τ σ) (MirUin k (i + t)) 1 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f hf
  classical
  have hsm₀ : IsSmooth (topRep τ W) := GlobalTheory.T.smooth_top_representation k i τ hτ
  have hsm : IsSmooth (fibAct t (topRep τ W)) := GlobalTheory.T.smooth_fibre_action k i t (topRep τ W) hsm₀
  have hsmP : IsSmooth (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) := fun v =>
    (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _ v).preimage (continuous_uMh (i + t))
  have hker : ∀ κ, fibLin τ σ hτ hσ κ f ∈ twKer (fibAct t (topRep τ W)) ⊤ 1 := fun κ =>
    mem_twKer_fibAct i t (topRep τ W) μ (fibLin τ σ hτ hσ κ f) (GlobalTheory.T.closure_kernel_mem_jacquet_kernel k i τ _ (hf κ))
  have hfin : ((fun κ => fibLin τ σ hτ hσ κ f) '' (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    rw [Set.image_image]
    exact GlobalTheory.T.finite_fibre_functions_compact k i t τ σ f
  have hF : ∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), ∀ y x,
      fibLin τ σ hτ hσ κ (MonoidHom.comp (prodPG τ σ) (uMh k (i + t)) y x) =
        fibAct t (topRep τ W) (mulH κ y) (fibLin τ σ hτ hσ κ x) := by
    intro κ _ y x
    apply Subtype.ext
    funext v
    exact GlobalTheory.T.fibre_function_unipotent_action k i t τ σ x y.toAdd κ v
  have hinj : ∀ x, (∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), fibLin τ σ hτ hσ κ x = 0) → x = 0 := by
    intro x hx
    exact GlobalTheory.T.induced_vanishing_on_compact k i t τ σ x fun κ hκ => congrArg Subtype.val (hx κ hκ)
  obtain ⟨T, hTn, hT⟩ := exists_sum_eq_zero_abs (i + t) (fibAct t (topRep τ W)) hsm
    (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) hsmP _ (fun _ h => h) (fibLin τ σ hτ hσ) hF hinj f
    (fun κ _ => hker κ) hfin
  exact mem_twKer_of_sum (prodPG τ σ) (MirUin k (i + t)) T hTn
    (fun y => ⟨uM k (i + t) y.toAdd, uM_mem k (i + t) y.toAdd⟩) f hT

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionEnlargeFiniteSet
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi.Integrals

variable {F : Type} [Field F] [NumberField F]

theorem integral_pi_unit {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (h : X → ℝ) :
    ∫ y : Unit → X, h (y ()) ∂(Measure.pi fun _ : Unit => μ) = ∫ x, h x ∂μ :=
  (measurePreserving_piUnique (fun _ : Unit => μ)).integral_comp' (f := MeasurableEquiv.piUnique _) h

theorem integral_comp_unit_mul {R : Type} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [MeasurableSpace R] [BorelSpace R] (b : Rˣ) (μ : Measure R) (f : R → ℝ) :
    ∫ y, f ((b : R) * y) ∂μ = ∫ y, f y ∂(μ.map fun y => (b : R) * y) := by
  let e : R ≃ₜ R :=
    { toEquiv := Units.mulLeft b
      continuous_toFun := show Continuous fun x => (b : R) * x from continuous_const.mul continuous_id
      continuous_invFun :=
        show Continuous fun x => ((b⁻¹ : Rˣ) : R) * x from continuous_const.mul continuous_id }
  exact (e.measurableEmbedding.integral_map (μ := μ) f).symm

def unitInf (a : (AF F)ˣ) : (Ainf F)ˣ where
  val := (a : AF F).1
  inv := ((a⁻¹ : (AF F)ˣ) : AF F).1
  val_inv := by
    have h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).1 = 1 := by simp; rfl
    exact h
  inv_val := by
    have h : (((a⁻¹ : (AF F)ˣ) : AF F) * (a : AF F)).1 = 1 := by simp; rfl
    exact h

theorem sigmaFinite_inf (li : Measure (Ainf F)) (h : li.IsAddHaarMeasure) : SigmaFinite li := by
  infer_instance

theorem sigmaFinite_fin (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v)) (h : l.IsAddHaarMeasure) :
    SigmaFinite l := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  infer_instance

theorem integral_mul_inf (li : Measure (Ainf F)) (h : li.IsAddHaarMeasure) (b : (Ainf F)ˣ)
    (G : Ainf F → ℝ) :
    ∫ y, G ((b : Ainf F) * y) ∂li = ‖((b⁻¹ : (Ainf F)ˣ) : Ainf F)‖ * ∫ y, G y ∂li := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hn : 0 ≤ ‖((b⁻¹ : (Ainf F)ˣ) : Ainf F)‖ := by
    rw [InfiniteAdeleRing.norm_def]
    exact Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  rw [integral_comp_unit_mul b li G, GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_infinite ⟨rfl⟩ b li h,
    integral_smul_measure, ENNReal.toReal_ofReal hn, smul_eq_mul]

theorem integral_mul_fin (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v))
    (h : l.IsAddHaarMeasure) (c : Fv F v) (hc : c ≠ 0) (f : Fv F v → ℝ) :
    ∫ y, f (c * y) ∂l = ‖c‖⁻¹ * ∫ y, f y ∂l := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have h1 := integral_comp_unit_mul (Units.mk0 c hc) l f
  simp only [Units.val_mk0] at h1
  rw [h1, GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v c hc l h, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul]
  simp

theorem integral_ind (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v)) (h : IsStdV v l)
    (c : Fv F v) (hc : c ≠ 0) :
    ∫ y, (if c * y ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) ∂l = ‖c‖⁻¹ := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (Fv F v)) :=
    (Valued.isOpen_valuationSubring _).measurableSet
  have h0 := integral_mul_fin v l h.1 c hc
    (fun s => if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0)
  have h1 : (fun s : Fv F v => if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) =
      (v.adicCompletionIntegers F : Set (Fv F v)).indicator 1 := by
    ext s
    simp [Set.indicator]
  have h2 : ∫ s, (if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) ∂l = 1 := by
    rw [h1, integral_indicator_one hO, Measure.real, h.2]
    simp
  rw [h0, h2, mul_one]

theorem norm_unitInf_inv (a : (AF F)ˣ) :
    ‖(((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F)‖ =
      (∏ w : InfinitePlace F, ‖(a : AF F).1 w‖ ^ w.mult)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [InfiniteAdeleRing.norm_def, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [← mul_pow, ← norm_mul]
  have h := IdeleGroup.infinite_mul_inv a w
  have h' : ((a⁻¹ : (AF F)ˣ) : AF F).1 w * (a : AF F).1 w = 1 := by rw [mul_comm]; exact h
  have : (((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F) w = ((a⁻¹ : (AF F)ˣ) : AF F).1 w := rfl
  rw [this, h', norm_one, one_pow]

theorem md_eq_of_off (a : (AF F)ˣ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hoff : ∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) :
    md a = (∏ w : InfinitePlace F, ‖(a : AF F).1 w‖ ^ w.mult) * ∏ v ∈ T, ‖(a : AF F).2 v‖ := by
  rw [md, IdeleGroup.ideleModule_eq]
  congr 1
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hT
  exact hv (IdeleGroup.norm_eq_one_of_mul_eq_one (IdeleGroup.finite_mul_inv a v)
    (hoff v hT).1 (hoff v hT).2)

theorem integrals_translates : ∀ (F : Type) [Field F] [NumberField F] (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)),
    IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    (∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li)) * ∏ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      (md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)) := by
  intro F _ _ li lam hli hlam S T G g a hST hoff
  haveI := sigmaFinite_inf li hli.1
  have hI : ∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li) =
      ‖(((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F)‖ * ∫ y, G y ∂li :=
    (integral_pi_unit li (fun x => G ((a : AF F).1 * x))).trans
      (integral_mul_inf li hli.1 (unitInf a) G)
  have hv : ∀ v, (a : AF F).2 v ≠ 0 := IdeleGroup.finite_ne_zero a
  have hP : ∀ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      ‖(a : AF F).2 v‖⁻¹ * (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) := by
    intro v _
    haveI := sigmaFinite_fin v (lam v) (hlam v).1
    by_cases hS : v ∈ S
    · have h1 := integral_pi_unit (lam v) (fun x => g v ((a : AF F).2 v * x))
      have h2 := integral_mul_fin v (lam v) (hlam v).1 _ (hv v) (g v)
      simp only [psiA, hS, if_true]
      rw [h1, h2]
    · have h1 := integral_pi_unit (lam v) (fun x =>
        if (a : AF F).2 v * x ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0)
      have h2 := integral_ind v (lam v) (hlam v) _ (hv v)
      simp only [psiA, hS, if_false]
      rw [h1, h2, mul_one]
  have hS' : ∏ v ∈ T, (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) = ∏ v ∈ S, ∫ s, g v s ∂(lam v) := by
    symm
    calc ∏ v ∈ S, ∫ s, g v s ∂(lam v)
        = ∏ v ∈ S, (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) :=
          Finset.prod_congr rfl fun v h => by simp [h]
      _ = _ := Finset.prod_subset hST fun v _ h => by simp [h]
  rw [hI, Finset.prod_congr rfl hP, Finset.prod_mul_distrib, hS', md_eq_of_off a T hoff,
    norm_unitInf_inv, mul_inv, Finset.prod_inv_distrib]
  ring

end GlobalTheory.CompanionTheory.BasePsi.Integrals
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneSiegelWeilThetaAverage
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem actW_rat_one {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (g : HA (AF F) σ J) (X : Fin 1 → Fin 1 → E) (a i : Fin 1) :
    actW (AF F) σ J g (ratTup (AF F) X) a i = (ue (AF F) σ J g : AF F ⊗[F] E) * inclR (AF F) (X a i) := by
  have e : ((ue (AF F) σ J g : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (HA.mat (AF F) σ J g).val 0 0 := by
    simp [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [e]
  simp only [actW, actTup, Matrix.mulVec, dotProduct, ratTup, Fin.sum_univ_one, Subsingleton.elim i 0,
    Subsingleton.elim a 0]

theorem mean_eq_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  intro F E _ _ _ _ _ σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 1
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 1 J hJ (AF F)
  obtain ⟨ac, -, -, -⟩ := hact 1
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨k1, -, -, -, -, -, -, k8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := k8 1 1
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨hφc, -, hφ0, -, hAS, hAoff⟩ := hT
  have hs : ∀ v, Continuous fun X : Fin 1 → Fin 1 → AF F ⊗[F] E => projV v (projFin X) := fun v => (t3 v).comp t2
  have hP : IsOpen {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
    have e : {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
        (⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' A v) ∩ intOff b S := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, intOff]
      refine ⟨fun h => ⟨fun v _ => h v, fun v hv => hAoff v hv ▸ h v⟩, fun h v => ?_⟩
      by_cases hv : v ∈ S
      · exact h.1 v hv
      · rw [hAoff v hv]; exact h.2 v hv
    rw [e]
    exact (isOpen_biInter_finset fun v hv => (hAS v hv).2.1.preimage (hs v)).inter (t5 S)
  have hPsi : Measurable (Psi φ A) :=
    (ENNReal.measurable_ofReal.comp (hφc.comp t1).measurable).indicator hP.measurableSet
  have hmul : Continuous fun (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (a i : Fin 1) => (x : AF F ⊗[F] E) * Y a i :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  set Φ : (Fin 1 → Fin 1 → AF F ⊗[F] E) → ℝ≥0∞ := fun Y => Psi φ A fun a i => (x : AF F ⊗[F] E) * Y a i with hΦd
  have hΦ : Measurable Φ := hPsi.comp hmul.measurable
  have hQ : MeasurableSet {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin fun a i => (x : AF F ⊗[F] E) * X a i) ∈ A v} :=
    (hP.preimage hmul).measurableSet
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hterm : ∀ (h : HA (AF F) σ J), Th φ A (x * ue (AF F) σ J h⁻¹) =
      ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _), Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) := fun h => by
    refine tsum_congr fun X => ?_
    simp only [hΦd]
    congr 1
    funext a i
    rw [actW_rat_one, Units.val_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · simp only [hterm]
    rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 1 _ Φ hΦ, mean, ← lintegral_indicator hQ]
    refine lintegral_congr fun X => ?_
    simp only [hΦd, Psi, Set.indicator, Set.mem_setOf_eq]
  · simp only [hterm]
    exact Measurable.ennreal_tsum fun X => hΦ.comp (ac.comp (continuous_inv.prodMk continuous_const)).measurable

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

theorem norm_theta {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (ε : ℝ) (w : InfinitePlace F) : ‖θ ε w‖ = |ε| := by
  have hw : w.IsReal := hF.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ρ : ℝ →+* ℝ := (e : w.Completion →+* ℝ).comp ((Pi.evalRingHom _ w).comp θ)
  have hρ : ρ ε = ε := by
    have : ρ = RingHom.id ℝ := Subsingleton.elim _ _
    rw [this]; rfl
  have hnorm : ‖θ ε w‖ = ‖e (θ ε w)‖ := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) _).symm
  rw [hnorm]
  change ‖ρ ε‖ = |ε|
  rw [hρ, Real.norm_eq_abs]

theorem norm_md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F,
    Continuous θ → ∀ r, IsRay θ r → (∀ (ε : ℝ) (w : InfinitePlace F), ‖θ ε w‖ = |ε|) ∧
      ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ _ r hr
  refine ⟨norm_theta hF θ, fun δ hδ => ?_⟩
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hmd : md (r δ) = (∏ w : InfinitePlace F, ‖(r δ : AF F).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ := IdeleGroup.ideleModule_eq _
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [h2]
    exact norm_one
  rw [hmd, hfin, mul_one, h1]
  simp only [norm_theta hF θ δ, abs_of_pos hδ]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsOfWeylHeisenbergProductStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_of_weyl_heisenberg_product : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K),
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows | exact GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows | (intros; apply GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows <;> assumption)
end
end

