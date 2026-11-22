import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0283
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace ENNReal NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

namespace GlobalTheory.PairLift.LowAllPf

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem kernel_zero : thetaKO ω g h 0 = 0 := by simp [thetaKO]

theorem kernel_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO, map_add]

theorem kernel_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO, map_sub]

theorem kernel_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO, map_smul]

end Kernel

theorem multT_apply_smooth_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT'.aut w), GlobalTheory.MultMem.isCuspFun_smul c (hT'.cusp w)⟩
  | add x y hx hy =>
    rw [map_add]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem liftInt_span_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, funext fun x => ?_⟩
    simp [Lift.liftInt, kernel_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (a + b) Φ x =
        Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x + Lift.liftInt ν 𝓕 (thetaKO ω) b Φ x := by
      simp only [Lift.liftInt, kernel_add, add_mul]
      exact integral_add (hI a ha.1 x) (hI b hb.1 x)
    simp [e, congrFun ha.2 x, congrFun hb.2 x]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (c • a) Φ x = c * Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x := by
      simp only [Lift.liftInt, kernel_smul, mul_assoc]
      exact integral_const_mul c _
    simp [e, congrFun ha.2 x]

theorem eq_zero_of_le_mul_all {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  rcases eq_or_ne K 0 with hK0 | hK0
  · have h1 := h 1 one_pos
    rw [hK0, zero_mul] at h1
    exact h1.trans zero_le
  · refine (h (ε / K) (ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') hK)).trans (le_of_eq ?_)
    exact ENNReal.mul_div_cancel hK0 hK

theorem liftInt_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hKt : (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (hL.decay_ne_top Φ hΦ A)
  funext x
  have hI : ∀ f', IsThetaFunO ψ V W f' → IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' => by
    simpa only [rTr, mul_one] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ δ : ℝ≥0∞, 0 < δ → ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ / height V x ^ A) ≤
      (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by
    intro δ hδ
    obtain ⟨g, hgU, hg0, hlt⟩ := happ d δ hδ
    have hfg : f - g ∈ thetaLevel ψ V W U := sub_mem hf hgU
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x := by
      have e' : Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x =
          Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x - Lift.liftInt ν 𝓕 (thetaKO ω) g Φ x := by
        simp only [Lift.liftInt, kernel_sub, sub_mul]
        exact integral_sub (hI f hf.1) (hI g hgU.1)
      rw [e', congrFun hg0 x, Pi.zero_apply, sub_zero]
    have h2 : ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x‖ / height V x ^ A) ≤
        growthSob θ V 0 A (lift ω ν 𝓕 (f - g) Φ) := by
      simp only [growthSob, wordSum_zero, growthSize]
      exact le_iSup (fun y => ENNReal.ofReal (‖lift ω ν 𝓕 (f - g) Φ y‖ / height V y ^ A)) x
    rw [e]
    calc _ ≤ _ := h2
      _ ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := hC (f - g) hfg Φ hΦ
      _ = (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * sobO ψ θ μ 𝓓 d (f - g) := by ring
      _ ≤ (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by gcongr
  have h0 := eq_zero_of_le_mul_all hKt key
  rw [ENNReal.ofReal_eq_zero] at h0
  have hpos : 0 < height V x ^ A := pow_pos (height_pos V x) A
  have h3 : ‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ ≤ 0 := by
    simpa using (div_le_iff₀ hpos).1 h0
  exact norm_le_zero_iff.1 h3

end GlobalTheory.PairLift.LowAllPf

namespace GlobalTheory.PairLift

theorem lowAll_of_lowFock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  intro D X hIn hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v f' hf
  obtain ⟨χS, χT, hW, -⟩ := id hω
  have hL := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hFv := LowAllPf.multT_apply_smooth_cusp θ M' ∅ 1 F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  obtain ⟨U, hU, hfU, happ⟩ := hIn.dense V' W A (Fr.ofModel M') θ ψ hW.std hθ μ 𝓓 hμ f' hf
  have hI : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa only [rTr, mul_one] using hL.integ f (F v) hf hFv x 1
  have hspan := LowAllPf.liftInt_span_zero hI
    (s := {g | ∃ f₀ P, IsVacF ψ θ A (Fr.ofModel M') f₀ ∧ f₀ ∈ thetaLevel ψ V' W U ∧
      g = ptF ψ θ A (Fr.ofModel M') f₀ P})
    (by
      rintro _ ⟨f₀, P, hv, -, rfl⟩
      exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hv.1 P,
        hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hv P⟩)
  refine LowAllPf.liftInt_zero_of_approx hL hFv hμ.1 hμ.2.1 hU hfU fun d δ hδ => ?_
  obtain ⟨g, hg, hgU, hlt⟩ := happ d δ hδ
  exact ⟨g, hgU, (hspan g hg).2, hlt⟩

end GlobalTheory.PairLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquations
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_realAd_mul (t : ℝ) (c : AF F) : evI F (realAd F t * c) = t • evI F c := by
  rw [← evIHom_apply, map_mul, evIHom_apply, evIHom_apply, Algebra.smul_def]
  congr 1
  simp [evI, realAd]

theorem realAd_mul_snd (t : ℝ) (c : AF F) : (realAd F t * c).2 = 0 := by
  show (realAd F t).2 * c.2 = 0
  simp [realAd]

theorem at_realAd_mul (t : ℝ) (c : AF F) : At (evI F) (realAd F t * c) := by
  intro b hb
  have h1 : b.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F b.1 = 0 := hb
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  rw [smul_eq_mul, ← mul_assoc]
  have : b * realAd F t = 0 := Prod.ext (by show b.1 * _ = 0; rw [h1, zero_mul]) (by show _ * (realAd F t).2 = 0; simp [realAd])
  rw [this, zero_mul]

def gam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (t : ℝ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ _ (y ⬝ᵥ fun i => evI F (w.2 i)) + t ^ 2 * Algebra.trace ℝ _ (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) : ℝ) : ℂ)) *
    f (y + t • fun i => evI F (w.1 i))

theorem gam_differentiableAt (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    DifferentiableAt ℝ (fun t => gam w f t y) 0 := by
  unfold gam
  fun_prop

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (t : ℝ) (f : SInf F κ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    schr ψ (realAd F t • w) (pureA F f g) x = gam w f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  have hK : x ⬝ᵥ (realAd F t • w).2 + ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2) =
      realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hev : evI F (realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))) =
      t • ((fun i => evI F (x i)) ⬝ᵥ (fun i => evI F (w.2 i)) + t • evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    rw [evI_realAd_mul]
    congr 1
    rw [← evIHom_apply, map_add, evIHom_apply, evIHom_apply, evI_realAd_mul, ← evIHom_apply (x ⬝ᵥ w.2),
      RingHom.map_dotProduct]
    rfl
  unfold schr pureA gam
  rw [hK, hψ.2.2 _ (at_realAd_mul _ _), hev]
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (realAd F t • w).1) i).1) =
      (fun i => evI F (x i)) + t • fun i => evI F (w.1 i) := by
    funext i
    show evIHom (x i + realAd F t * w.1 i) = evI F (x i) + t • evI F (w.1 i)
    rw [map_add, evIHom_apply, evIHom_apply, evI_realAd_mul]
  have hg : (fun i => ((x + (realAd F t • w).1) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (realAd F t * w.1 i).2 = (x i).2
    rw [realAd_mul_snd, add_zero]
  rw [hf, hg]
  simp only [map_smul, map_add, smul_eq_mul]
  ring_nf

end GlobalTheory.VacFactor

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def dgam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  deriv (fun t => gam w f t y) 0

theorem exists_indep {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ k, g k ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ LinearIndependent ℂ g ∧ Φ = ∑ k, pureA F (f k) (g k) := by
  obtain ⟨m₀, c, p, hp⟩ := Submodule.mem_span_set'.mp hΦ
  choose f₀ g₀ hg₀ hp₀ using fun i => (p i).2
  set f₁ : Fin m₀ → SInf F κ := fun i => c i • f₀ i
  have hΦ' : Φ = ∑ i, pureA F (f₁ i) (g₀ i) := by
    rw [← hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp₀ i]
    funext x
    simp [f₁, pureA, mul_assoc]
  set V := Submodule.span ℂ (Set.range g₀)
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range g₀)
  let b := Module.finBasis ℂ V
  have hmem : ∀ i, g₀ i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  let a : Fin m₀ → Fin (Module.finrank ℂ V) → ℂ := fun i j => b.repr ⟨g₀ i, hmem i⟩ j
  have hg : ∀ i z, g₀ i z = ∑ j, a i j * (b j : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z := by
    intro i z
    have := congrArg (fun v : V => (v : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z) (b.sum_repr ⟨g₀ i, hmem i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨Module.finrank ℂ V, fun j => ∑ i, a i j • f₁ i, fun j => (b j : _), fun j => ?_, ?_, ?_⟩
  · exact (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hg₀ i)) (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · rw [hΦ']
    funext x
    simp only [Finset.sum_apply, pureA, hg, Finset.mul_sum, Finset.sum_mul, SchwartzMap.sum_apply,
      SchwartzMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (t : ℝ) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    M.heisLine ψ u t (pureA F f g) x = gam (M.co.e u) f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  unfold Model.heisLine Darboux.rho
  rw [map_smul, schr_pureA ψ hψ]

theorem hasDerivAt_heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (pureA F f g) x)
      (dgam (M.co.e u) f (fun i => evI F (x i)) * g (fun i => (x i).2)) 0 := by
  simp only [heisLine_pureA M ψ hψ]
  exact (gam_differentiableAt _ _ _).hasDerivAt.mul_const _

theorem hasDerivAt_heisLine_sum (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (g : Fin m → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x)
      (∑ k, dgam (M.co.e u) (f k) (fun i => evI F (x i)) * g k (fun i => (x i).2)) 0 := by
  have e : (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x) =
      fun t => ∑ k, M.heisLine ψ u t (pureA F (f k) (g k)) x := by
    funext t
    simp only [Model.heisLine, Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]
  rw [e]
  exact HasDerivAt.fun_sum fun k _ => hasDerivAt_heisLine_pureA M ψ hψ u (f k) (g k) x

end GlobalTheory.VacFactor

open GlobalTheory.VacFactor in

theorem GlobalTheory.VacFactor.mem_span_of_isGaussEq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hψ Φ hΦ hG
  obtain ⟨m, f, g, hg, hgi, rfl⟩ := exists_indep hΦ
  obtain ⟨ε, hε⟩ := hG
  let mk : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) →
      (Fin n × Fin d → AF F) :=
    fun y z i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), z i)
  have hmk1 : ∀ y z, (fun i => evI F (mk y z i)) = y := fun y z => by
    funext i
    simp [mk, evI]
  have hmk2 : ∀ y z, (fun i => (mk y z i).2) = z := fun y z => rfl
  have key : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
      ∀ k y, dgam (M.co.e u') (f k) y = Complex.I * dgam (M.co.e u) (f k) y := by
    intro u u' hu hu' hr k y
    have h0 : ∑ k, (dgam (M.co.e u') (f k) y - Complex.I * dgam (M.co.e u) (f k) y) • g k = 0 := by
      funext z
      have e := hε u u' hu hu' hr (mk y z)
      rw [(hasDerivAt_heisLine_sum M ψ hψ u' f g (mk y z)).deriv,
        (hasDerivAt_heisLine_sum M ψ hψ u f g (mk y z)).deriv, hmk1, hmk2] at e
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
      rw [e, Finset.mul_sum]
      simp only [mul_assoc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hgi _ h0 k)
  have hgne : ∀ k, ∃ z, g k z ≠ 0 := fun k => by
    by_contra h
    push Not at h
    exact hgi.ne_zero k (funext h)
  have gauss : ∀ k, M.IsGauss ψ τ (f k) := by
    intro k
    obtain ⟨z₀, hz₀⟩ := hgne k
    refine ⟨ε, fun u u' hu hu' hr f₁ f₁' h1 h1' => ?_⟩
    have hR : Rest (evI F) (⇑(f k)) (fun x : Fin n × Fin d → AF F => g k (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f k, g k, hg k, rfl⟩⟩
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h0 : evI F (show AF F from ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))) = 0 := by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _
        have := congrArg (fun v : Fin n × Fin d → AF F => (v i).2) (hz _ h0)
        change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at this
        simpa using this
      have hxz : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [hz2, add_zero]
      exact congrArg (g k) hxz
    have hD : ∀ (v : Matrix (Fin n) (Fin d) (AE F E)) (f₂ : SInf F (Fin n × Fin d)),
        ActsD (evI F) (M.heisLine ψ v) (⇑(f k)) (⇑f₂) → ∀ y, f₂ y = dgam (M.co.e v) (f k) y := by
      intro v f₂ h y
      have a := h _ hR (mk y z₀)
      have b := hasDerivAt_heisLine_pureA M ψ hψ v (f k) (g k) (mk y z₀)
      have := a.unique b
      simp only [tens, hmk1, hmk2] at this
      exact mul_right_cancel₀ hz₀ this
    refine DFunLike.ext _ _ fun y => ?_
    rw [hD u' f₁' h1' y, key u u' hu hu' hr k y, ← hD u f₁ h1 y]
    simp
  refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, g k, ?_, hg k, rfl⟩
  exact Submodule.mem_sInf.mpr fun N hN => hN.1 _ (gauss k)

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagParabolicIffSplitPlaceChain
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)

theorem exists_mulVec_eq_of_maps {K : Type} [Field K] {n : ℕ} (M : GL (Fin n) K) (S : Submodule K (Fin n → K))
    (hS : ∀ u ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ S) :
    ∀ u ∈ S, ∃ u₀ ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u₀ = u := by
  intro u hu
  let f : S →ₗ[K] S := (M : Matrix (Fin n) (Fin n) K).mulVecLin.restrict hS
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have e : (M : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K) = (M : Matrix (Fin n) (Fin n) K) *ᵥ (b : Fin n → K) :=
      congrArg Subtype.val hab
    have e2 := congrArg (fun x => ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) e
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using e2
  obtain ⟨a, ha⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨u, hu⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

theorem splitHom_mulVec_mem_wPart (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v) {W : Submodule E V.V}
    {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v} (hg : g ∈ parab hc V (Fv F v) W) {u : Fin V.rank → Fv F v}
    (hu : u ∈ wPart τ W) :
    ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u
      ∈ wPart τ W := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact ⟨act hc V g y, mem_parab_iff_maps.1 hg y hy, splitVec_matHom_mulVec τ g y⟩

theorem flagChain_eq_X (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨i, by omega⟩ = wPart τ (𝔉.X i) := by
  rw [flagChain_of_le 𝔉 τ (show (i : ℕ) ≤ 𝔉.k by omega)]

theorem flagChain_eq_perp (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨2 * 𝔉.k + 1 - i, by omega⟩ = wPart τ (perp V (𝔉.X i)) := by
  rw [flagChain_of_lt 𝔉 τ (show 𝔉.k < 2 * 𝔉.k + 1 - (i : ℕ) by omega)]
  congr 3
  ext
  simp only
  omega

theorem mem_par_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.par hc (Fv F v) ↔ ∀ j, ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
    · rw [flagChain_of_le 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (Subgroup.mem_iInf.1 hg _) hu
    · rw [flagChain_of_lt 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (parab_le_perp (Subgroup.mem_iInf.1 hg _)) hu
  · intro H
    refine Subgroup.mem_iInf.2 fun i => mem_parab_iff_maps.2 fun y hy => ?_
    have H1 := H ⟨i, by omega⟩
    rw [flagChain_eq_X] at H1
    have H2 := H ⟨2 * 𝔉.k + 1 - i, by omega⟩
    rw [flagChain_eq_perp] at H2
    have key : ∀ τ' : E →ₐ[F] Fv F v, splitVec τ' (act hc V g y) =
        ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ' g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v))
          *ᵥ splitVec τ' y := fun τ' => splitVec_matHom_mulVec τ' g y
    rw [mem_extSub_iff_split hc h τ] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [key]
      exact H1 _ hy1
    · rw [key, mem_wPart_comp_iff hc h hJ τ]
      intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := exists_mulVec_eq_of_maps _ _ H2 u hu
      rw [pairing_splitHom]
      exact (mem_wPart_comp_iff hc h hJ τ).1 hy2 u₀ hu₀

end GlobalTheory.SplitFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevelIndicatorCoefficientTestLeDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.PoinTerm

theorem norm_coef_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  intro D θ hθ V S M K v hv b hb
  choose C hC using fun τ => (hv τ).2 (b τ) (hb τ)
  have hpos : ∀ (τ : D.what₂.Tau) (x : GA D V), 0 < (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) := fun τ x =>
    pow_pos (add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)) _
  have hle : ∀ (τ : D.what₂.Tau) (x : GA D V), ‖⟪v τ, M.rep τ (cmp θ τ x) (b τ)⟫_ℂ‖ * (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) ≤ C τ :=
    fun τ x => hC τ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
  have h0 : ∀ τ, 0 ≤ C τ := fun τ => (mul_nonneg (norm_nonneg _) (hpos τ 1).le).trans (hle τ 1)
  have hP : 0 ≤ ∏ τ, C τ := Finset.prod_nonneg fun τ _ => h0 τ
  refine ⟨∏ τ, C τ, hP, fun x => ?_⟩
  unfold coef
  split_ifs
  · unfold coefR
    rw [norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun τ _ => norm_nonneg _) fun τ _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (hpos τ x)]
    exact hle τ x
  · rw [norm_zero]
    exact mul_nonneg hP (Finset.prod_nonneg fun τ _ => (inv_pos.2 (hpos τ x)).le)

end GlobalTheory.PoinTerm
end

