import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PositionOneOfUnique
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedModuleNontrivial
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.IndNonzero

theorem mem_leviOne_of_mem_parab_KG {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) {p : UJ ε} (hp : p ∈ parab ε W) (hk : p ∈ KG ε) :
    p ∈ leviOne ε W := by
  obtain ⟨u, hu, m, hm, x, t, ht, rfl⟩ := exists_langlands_decomp hW hj hp
  obtain ⟨h, -, h1, hK, hh⟩ := exists_height hW hj
  have hx : x = 0 := by
    have e1 := hh u hu m hm x t ht 1
    have e2 := hK 1 _ hk
    rw [mul_one] at e1
    rw [one_mul] at e2
    rw [e2, h1, add_zero] at e1
    exact e1.symm
  subst hx
  have ht1 : t = 1 := (existsUnique_isSplit hW 0).unique ht isSplit_one
  subst ht1
  rw [mul_one] at hk ⊢
  have hk' : u * m ∈ maxK ε := by rw [← KG_eq]; exact hk
  rw [GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW u hu m hm.1 hk', one_mul]
  exact hm

theorem continuous_apply_of_isURepOn {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℂ)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}
    (hσ : IsURepOn S σ) {X : Type} [TopologicalSpace X] {mf : X → Matrix (Fin n) (Fin n) ℂ} {wf : X → V}
    (hm : Continuous mf) (hS : ∀ x, mf x ∈ S) (hw : Continuous wf) : Continuous fun x => σ (mf x) (wf x) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have h1 : ContinuousAt (fun x => σ (mf x) (wf x0)) x0 :=
    ((hσ.2.2 (wf x0)).comp_continuous hm hS).continuousAt
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
  have h2 : Filter.Tendsto (fun x => ‖wf x - wf x0‖) (nhds x0) (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hw.continuousAt
  refine squeeze_zero (g := fun x => ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ + ‖wf x - wf x0‖)
    (fun _ => norm_nonneg _) (fun x => ?_) (by have := h1.add h2; rwa [add_zero] at this)
  calc ‖σ (mf x) (wf x) - σ (mf x0) (wf x0)‖
      = ‖σ (mf x) (wf x - wf x0) + (σ (mf x) (wf x0) - σ (mf x0) (wf x0))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖σ (mf x) (wf x - wf x0)‖ + ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ := norm_add_le _ _
    _ = _ := by rw [hσ.2.1 _ (hS x)]; ring

end GlobalTheory.IndNonzero

namespace GlobalTheory.IndNonzero

theorem exists_equivariant {n : ℕ} {ε : Fin n → Bool} (D : Datum ε) :
    ∃ F : UJ ε → D.V, Continuous F ∧ F 1 ≠ 0 ∧ ∀ u ∈ flagN ε D.W, ∀ m ∈ leviOne ε D.W, ∀ x t,
      IsSplit ε D.W x t → ∀ g, F (u * m * t * g) = D.σ (uMat m) (F g) := by
  classical
  obtain ⟨hU, -⟩ := D.temp.2.2
  have hW := D.flag
  have hj := D.pos
  obtain ⟨φ, hφc, hφ1, hφm⟩ := GlobalTheory.T.continuous_section_levi_equivariant n ε D
  obtain ⟨μ, hμc, hμM, hμmul, hμs⟩ := GlobalTheory.T.parabolic_projection_to_levi n D.a ε D.j D.W hW hj
  have hPK := fun p hp hk => mem_leviOne_of_mem_parab_KG hW hj (p := p) hp hk
  have hσmul : ∀ m ∈ leviOne ε D.W, ∀ m' ∈ leviOne ε D.W, ∀ w,
      D.σ (uMat (m * m')) w = D.σ (uMat m) (D.σ (uMat m') w) := by
    intro m hm m' hm' w
    rw [uMat_mul, hU.1.2 _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩]
    rfl
  have h1N : (1 : UJ ε) ∈ flagN ε D.W := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩
  have hμid : ∀ m ∈ leviOne ε D.W, μ m = m := fun m hm => by
    simpa using (hμs 1 h1N m hm 0 1 isSplit_one).2
  have dec : ∀ g : UJ ε, ∃ p ∈ parab ε D.W, ∃ k ∈ KG ε, g = p * k := fun g => by
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g
    refine ⟨g * k⁻¹, hp, k, ?_, by group⟩
    rw [← SetLike.mem_coe, KG_eq]
    exact hk
  have wd : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, ∀ p' ∈ parab ε D.W, ∀ k' ∈ KG ε, p * k = p' * k' →
      D.σ (uMat (μ p)) (φ k) = D.σ (uMat (μ p')) (φ k') := by
    intro p hp k hk p' hp' k' hk' e
    have hck : p'⁻¹ * p = k' * k⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    have hcP : p'⁻¹ * p ∈ parab ε D.W := mul_mem (inv_mem hp') hp
    have hcK : p'⁻¹ * p ∈ KG ε := hck ▸ mul_mem hk' (inv_mem hk)
    have hcM := hPK _ hcP hcK
    have h1 : μ p = μ p' * (p'⁻¹ * p) := by
      conv_lhs => rw [show p = p' * (p'⁻¹ * p) by group]
      rw [hμmul p' hp' _ hcP, hμid _ hcM]
    have h2 : φ k' = D.σ (uMat (p'⁻¹ * p)) (φ k) := by
      rw [← hφm _ hcM hcK, hck, inv_mul_cancel_right]
    rw [h1, hσmul _ (hμM p' hp') _ hcM, h2]
  choose pp hpp kk hkk hpk using dec
  let F : UJ ε → D.V := fun g => D.σ (uMat (μ (pp g))) (φ (kk g))
  have hF : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, F (p * k) = D.σ (uMat (μ p)) (φ k) := fun p hp k hk =>
    wd _ (hpp _) _ (hkk _) p hp k hk (hpk (p * k)).symm
  have hFc : Continuous F := by
    refine GlobalTheory.T.continuous_of_iwasawa_continuous n D.a ε D.j D.W hW D.V F ?_
    have : (fun q : parab ε D.W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) =
        fun q => D.σ (uMat (μ q.1)) (φ q.2) := funext fun q => hF _ q.1.2 _ q.2.2
    rw [this]
    refine continuous_apply_of_isURepOn hU (mf := fun q : parab ε D.W × KG ε => uMat (μ q.1)) (wf := fun q => φ q.2) ?_ ?_ ?_
    · exact continuous_uMat.comp ((hμc.comp_continuous continuous_subtype_val fun p => p.2).comp continuous_fst)
    · exact fun q => ⟨μ q.1, hμM _ q.1.2, rfl⟩
    · exact hφc.comp (continuous_subtype_val.comp continuous_snd)
  refine ⟨F, hFc, ?_, fun u hu m hm x t ht g => ?_⟩
  · have := hF 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    rw [this, hμid 1 (one_mem _), uMat_one, hU.1.1, ContinuousLinearMap.one_apply]
    exact hφ1
  · obtain ⟨hP, hμ⟩ := hμs u hu m hm x t ht
    have e : u * m * t * pp g * kk g = u * m * t * g := by rw [mul_assoc (u * m * t), ← hpk g]
    rw [← e, hF _ (mul_mem hP (hpp g)) _ (hkk g), hμmul _ hP _ (hpp g), hμ, hσmul _ hm _ (hμM _ (hpp g))]

theorem indModule_nontrivial : ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), Nontrivial I.H := by
  intro n ε I
  obtain ⟨F, hFc, hF1, hFl⟩ := exists_equivariant I.toDatum
  obtain ⟨e, he, he1, -⟩ := exists_spherical I.flag I.pos I.s
  have hf : (fun g => e g • F g) ∈ I.fns := by
    rw [mem_indFun_top]
    refine ⟨(mem_indFun_top.1 he).1.smul hFc, fun u hu m hm x t ht g => ?_⟩
    have := (mem_indFun_top.1 he).2 u hu m hm x t ht g
    simp only [ContinuousLinearMap.one_apply, smul_eq_mul] at this
    rw [this, hFl u hu m hm x t ht g, map_smul, smul_smul]
  have hpos := GlobalTheory.T.induced_function_l2_positive n ε I.toDatum _ hf 1 (by simpa [he1] using hF1)
  have hι : I.ι ⟨_, hf⟩ ≠ 0 := by
    intro h0
    have := I.model.norm_sq ⟨_, hf⟩
    rw [h0, norm_zero, zero_pow two_ne_zero] at this
    exact hpos.ne this
  exact nontrivial_of_ne _ _ hι

end GlobalTheory.IndNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRadicalSpanGMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesRadical

theorem isRadical_span_g_mul : ∀ (D : D7),
    (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}).IsRadical := by
  intro D
  have hrad : ∀ i : Fin 2, (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}).IsRadical := fun i =>
    GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver D.host.E (D.host.g i) (D.host.g_prime i)
      ((Formalism.MainNotions.Inhab.primesOver_ncard D.host.E (D.host.g i) (D.host.g_prime i)).trans (D.nd.g_split i))
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  have hsup : Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)} ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    have h1 : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
      have h2 := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
      simpa using h2
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_span_singleton_iff _ _).2 h1)
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, Ideal.mul_eq_inf_of_coprime hsup]
  exact (hrad 0).inf (hrad 1)

end GlobalTheory.TypePrimesRadical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunOPlaceModelApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceThetaVal
open GlobalTheory.PlaceVec GlobalTheory.PlaceModel GlobalTheory.AdelicLatMove

theorem isThetaFunO_placeModel_apply : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (A B : HSp D)
    (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ (e : AE D) (f₀ Φ : WO A B → ℂ) (Tm : (WO A B → ℂ) →ₗ[ℂ] (WO A B → ℂ)),
    e * e = e → infPart D e = 0 →
    IsPlaceModel ψ (symplO A B) (heisO ψ A B) e (latO A B (ΛA : Set (Fin A.rank → D.host.E)) (ΛB : Set (Fin B.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    IsThetaFunO ψ A B f₀ →
    IsSBHalf e (latO A B (ΛA : Set (Fin A.rank → D.host.E)) (ΛB : Set (Fin B.rank → D.host.E)) fun _ => True) Φ →
    IsThetaFunO ψ A B (Tm Φ) := by
  intro D ψ hψ S T ΛS ΛT hS hT a f₀ Φ Tm ha hinf h₁ hf₀ hΦ
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hmul := exists_nsmul_mem_latO hS.1 hT.1
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      b • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T b := fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  have ha' : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  have hb := isBichar_symplO S T ψ
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ, ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (half_infPart hinf hu.2)).1 hu.1 y hy
  have hmem := mem_waveSpan (X := half S T a) (Y := half S T (cA D a)) (L := Λ ⊓ half S T a)
    (L' := Λ ⊓ half S T (cA D a)) hb inf_le_right inf_le_right (fun u hu y hy => hLL' u hu y hy.1)
    (fun x hx h => ⟨(hdual x (half_infPart hinf hx)).2 fun u hu => by
      have := h _ (hsm ha' u hu)
      rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩)
    (half_div S T a) (half_div S T _) tf (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => a • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, a • u, hsm ha u hu, ?_⟩
      have := (mem_half S T).1 ht.2
      rw [← this, htr, smul_add, smul_comm a k u])
    Φ (fun t ht => (isHalf_iff S T).1 (hΦ.1 t ht)) _ hΦ.2.choose_spec.1
      (fun u hu => hΦ.2.choose_spec.2.1 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨hΦ.2.choose_spec.2.2 t ht, (half S T a).nsmul_mem ((isHalf_iff S T).1 (hΦ.1 t ht)) _⟩
  let P : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T (Tm g)}
      add_mem' := fun {g g'} hg hg' => by
        show IsThetaFunO ψ S T (Tm (g + g'))
        rw [map_add]; exact GlobalTheory.OrientedHeis.theta_add hg hg'
      zero_mem' := by
        show IsThetaFunO ψ S T (Tm 0)
        rw [map_zero]; exact GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c g hg => by
        show IsThetaFunO ψ S T (Tm (c • g))
        rw [map_smul]; exact GlobalTheory.OrientedHeis.theta_smul c hg }
  have hsub : waveSpan (fun x y => ψ (symplO S T x y)) (half S T a) (half S T (cA D a)) (Λ ⊓ half S T a) ≤ P := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hSB : IsSBHalf a Λ fun t => ψ (symplO S T t y) * halfInd a Λ t := by
      obtain ⟨k, hk, hky⟩ := hmul y (half_infPart (infPart_cA hinf) hy)
      have hne : ∀ t, ψ (symplO S T t y) * halfInd a Λ t ≠ 0 → t ∈ Λ ⊓ half S T a := fun t ht => by
        by_contra hn
        rw [halfInd_eq_ind, ind, if_neg hn, mul_zero] at ht
        exact ht rfl
      refine ⟨fun t ht => (isHalf_iff S T).2 (hne t ht).2, k, hk, fun u hu hu' t => ?_,
        fun t ht => nsmul_mem (hne t ht).1 k⟩
      have hu'' : u ∈ Λ ⊓ half S T a := ⟨hu, (isHalf_iff S T).1 hu'⟩
      have e1 := hb.left t (k • u) y
      have e2 := hb.nsmul k u y
      beta_reduce at e1 e2 ⊢
      rw [e1, e2, hLL' u hu'' _ hky, mul_one, halfInd_eq_ind, ind_add _ _ (nsmul_mem hu'' k)]
    have key : Tm (wave (fun x y => ψ (symplO S T x y)) (Λ ⊓ half S T a) x y) = heisO ψ S T x (heisO ψ S T y f₀) := by
      have e1 := h₁.trans _ hSB x ((isHalf_iff S T).2 hx)
      have e2 := h₁.modul _ (GlobalTheory.isSBHalf_halfInd a Λ) y ((isHalf_iff S T).2 hy)
      have e3 := h₁.vac
      rw [one_smul] at e3
      rw [e2, e3, halfInd_eq_ind] at e1
      exact e1
    show IsThetaFunO ψ S T (Tm _)
    rw [key]
    exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ y) x
  exact hsub hmem

end GlobalTheory.PlaceThetaVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsometryIntertwinesEnveloping
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.ActUIso

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem adjoint_comp_isometry (T : H' →ₗᵢ[ℂ] H) (v : H') :
    (ContinuousLinearMap.adjoint T.toContinuousLinearMap) (T v) = v := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

theorem deriv_isometry_comp (T : H' →ₗᵢ[ℂ] H) (f : ℝ → H') (t : ℝ) :
    deriv (fun s => T (f s)) t = T (deriv f t) := by
  by_cases hf : DifferentiableAt ℝ f t
  · have := (T.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
    exact this.deriv
  · have hTf : ¬ DifferentiableAt ℝ (fun s => T (f s)) t := by
      intro h
      apply hf
      have h2 := ((ContinuousLinearMap.adjoint T.toContinuousLinearMap).restrictScalars ℝ).differentiableAt.comp t h
      have e : f = (⇑(ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.adjoint T.toContinuousLinearMap)) ∘ fun s ↦ T (f s)) := by
        funext s
        simp [adjoint_comp_isometry]
      rw [e]; exact h2
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hTf, map_zero]

end GlobalTheory.ActUIso

namespace GlobalTheory.ActUIso

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem inG_smul_add_theta {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y)) := by
  have hJ := Jm_conjTranspose ε
  have hJJ := Jm_mul_self ε
  unfold inG PI.DSInfCharCap.thetaJ
  set J := Jm ε
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  have : (Y + -(J * Yᴴ * J))ᴴ * J + J * (Y + -(J * Yᴴ * J)) = 0 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hJ,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    abel
  rw [this, smul_zero]

theorem inG_smul_sub_theta {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y)) := by
  have hJ := Jm_conjTranspose ε
  have hJJ := Jm_mul_self ε
  unfold inG PI.DSInfCharCap.thetaJ
  set J := Jm ε
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.conj_I]
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, neg_smul, neg_add_eq_sub, ← smul_sub]
  have : J * (Y - -(J * Yᴴ * J)) - (Y - -(J * Yᴴ * J))ᴴ * J = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hJ,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    abel
  rw [this, smul_zero]

theorem dsig_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (w : H') :
    PI.PhMeasCore.dsig ρ X (T w) = T (PI.PhMeasCore.dsig ρ' X w) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • X)) (T w)) =
      fun t : ℝ => T (ρ' (NormedSpace.exp ((t : ℂ) • X)) w) := by
    funext t
    have h := hT (expG ε X t) w
    have h2 : uMat (expG ε X t) = NormedSpace.exp ((t : ℂ) • X) := toM_expG ε X t hX
    rw [h2] at h
    exact h.symm
  rw [e, deriv_isometry_comp]

theorem dsigC_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (Y : Matrix (Fin n) (Fin n) ℂ) (w : H') :
    PI.DSInfCharCap.dsigC ε ρ Y (T w) = T (PI.DSInfCharCap.dsigC ε ρ' Y w) := by
  unfold PI.DSInfCharCap.dsigC
  rw [dsig_intertwine ε ρ ρ' T hT _ (inG_smul_add_theta ε Y),
    dsig_intertwine ε ρ ρ' T hT _ (inG_smul_sub_theta ε Y), map_add, map_smul]

theorem dsigCW_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H') :
    PI.DSInfCharCap.dsigCW ε ρ l (T w) = T (PI.DSInfCharCap.dsigCW ε ρ' l w) := by
  induction l with
  | nil => rfl
  | cons Y l ih =>
    simp only [PI.DSInfCharCap.dsigCW]
    rw [ih, dsigC_intertwine ε ρ ρ' T hT]

theorem actU_isometry : ∀ {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H), (∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) → ∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (w : H'), actU ε ρ p (T w) = T (actU ε ρ' p w) := by
  intro n ε H H' _ _ _ _ _ _ ρ ρ' T hT p w
  unfold actU
  simp only [Finsupp.sum, map_sum, map_smul, dsigCW_intertwine ε ρ ρ' T hT]

end GlobalTheory.ActUIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportOfPolarisationIdealTimesLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTransport_of_polarisationIdealTimesLattice : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)), IsAA Λ ΛT → IsMov m Λ Λ → IsMov m ΛT ΛT := by
  first | exact @GlobalTheory.LevMoveAA.isMov_of_isAA | exact GlobalTheory.LevMoveAA.isMov_of_isAA | (intros; apply GlobalTheory.LevMoveAA.isMov_of_isAA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinctStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAndTwistPlaces_split_distinct : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) ∧ Set.InjOn (fun PP : Pl D.host.E => PP.under (𝓞 D.host.F)) ↑(R.Pg ∪ R.Q t) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, (Ideal.primesOver (PP.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2 ∧ Nat.card (kP PP) = Ideal.absNorm (PP.under (𝓞 D.host.F)).asIdeal := by
  first | exact @GlobalTheory.TwistTypePlaces.places_split | exact GlobalTheory.TwistTypePlaces.places_split | (intros; apply GlobalTheory.TwistTypePlaces.places_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelMultiplicityStableUnderActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMultiplicity_stable_under_action : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (g0 : Formalism.L2.DIV.G0 L.Pg L.r), ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∃ T' ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ v, T' v = actG0 V β L g0 (T v) := by
  first | exact @GlobalTheory.FlagAct.finiteGroupAction_preserves_principalFlagMultiplicity | exact GlobalTheory.FlagAct.finiteGroupAction_preserves_principalFlagMultiplicity | (intros; apply GlobalTheory.FlagAct.finiteGroupAction_preserves_principalFlagMultiplicity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPlaces

theorem pg_not_isConjPl : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ PP hP PP' hP'
  exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg PP hP PP' hP'

end GlobalTheory.SeeConjPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplierStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  first | exact @GlobalTheory.HatPoint.mem_hatA_of_div | exact GlobalTheory.HatPoint.mem_hatA_of_div | (intros; apply GlobalTheory.HatPoint.mem_hatA_of_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemMaximalCompactOfMapsFockVectorToFockStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximalCompact_of_maps_fockVector_to_fock : ∀ (n : ℕ) (ε : Fin n → Bool) (fr G : Matrix (Fin n) (Fin n) ℂ) (σ Z : Type) [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (Z → ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (MvPolynomial σ ℂ)), IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → Function.Injective pt → R 1 = 1 → (∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, R (g * g') = R g * R g') → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ φ z, HasDerivAt (fun t : ℝ => R (NormedSpace.exp (t • X)) (pt φ) z) (pt (L X φ) z) 0) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R (fr⁻¹ * k * fr) (pt φ) = pt ψ) → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → (∃ j k, ε j ≠ ε k ∧ (fr * X * fr⁻¹) j k ≠ 0 ∧ (fr * X * fr⁻¹) k j ≠ 0) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ m : ℕ, (L X ^ m) φ ∈ F) → ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ φ φ', φ ≠ 0 → pt φ' = R g (pt φ) → ∃ k ∈ Formalism.REAL.Kset ε, g = fr⁻¹ * k * fr := by
  first | exact @GlobalTheory.Chain.RealIt.CompactStab.mem_compact | exact GlobalTheory.Chain.RealIt.CompactStab.mem_compact | (intros; apply GlobalTheory.Chain.RealIt.CompactStab.mem_compact <;> assumption)
end

