import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0360
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0366
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddingsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgWeightF_weightTensorDualRepOfEmbeddings : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), NX.IsAlgWeightF L n K (GlobalTheory.AlgWtF.wtRepF emb lam) := by
  first | exact @GlobalTheory.AlgWtF.wtRepF_alg | exact GlobalTheory.AlgWtF.wtRepF_alg | (intros; apply GlobalTheory.AlgWtF.wtRepF_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLiftGelfandInvariantFiniteOfFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftFin

variable {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
  {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)}

theorem word_ker (hκ : IsKerSys θ V W κ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (f : M) : ∃ f', ∀ h, word θ V l (fun g => κ f g h) = fun g => κ f' g h := by
  induction l with
  | nil => exact ⟨f, fun _ => rfl⟩
  | cons p l ih =>
    obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨f'', e'⟩ := hκ.derV p.1 p.2 (hl p List.mem_cons_self) f'
    refine ⟨f'', fun h => ?_⟩
    change Rder θ V p.1 p.2 (word θ V l fun g => κ f g h) = _
    rw [e h]
    funext g
    exact (e' g h).deriv

theorem isMod_ker (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (f : M) (h : GA D W) : IsMod θ V fun g => κ f g h := by
  have hc : ∀ f, Continuous fun g => κ f g h := fun f => (hκ.cont f).comp (Continuous.prodMk_left h)
  refine ⟨GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ V (Set.range fun f g => κ f g h) ?_ ?_ _ ⟨f, rfl⟩, fun γ hγ g => ?_, fun l hl => ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact hc f
  · rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hκ.derV τ X hX f
    exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
  · simpa using hκ.left f γ hγ 1 (one_mem _) g h
  · obtain ⟨f', e⟩ := word_ker hκ l hl f
    obtain ⟨N, hN⟩ := hκ.growth
    obtain ⟨C, hC⟩ := hN f'
    rw [e h]
    refine ⟨hc f', N, C * (height θ W h : ℝ) ^ N, fun g => (hC g h).trans_eq ?_⟩
    ring

variable (κ) in

def lift (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (f : M) (F : GA D V → ℂ) : GA D W → ℂ :=
  fun h => ∫ g in 𝓕, κ f g h * F g ∂μ

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem lift_add_left (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (f f' : M) : lift κ μ 𝓕 (f + f') F = lift κ μ 𝓕 f F + lift κ μ 𝓕 f' F := by
  have I := (GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1
  funext h
  simp only [lift, map_add, Pi.add_apply, add_mul]
  exact integral_add (I f h) (I f' h)

theorem lift_add_right (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F F' : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (hF' : F' ∈ Decay θ V) (f : M) :
    lift κ μ 𝓕 f (F + F') = lift κ μ 𝓕 f F + lift κ μ 𝓕 f F' := by
  funext h
  simp only [lift, Pi.add_apply, mul_add]
  exact integral_add ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1 f h)
    ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F' hF').1 f h)

theorem lift_smul_left (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 (c • f) F = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem lift_smul_right (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 f (c • F) = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

variable (θ κ μ 𝓕) in

def Compat (T : (GA D W → ℂ) → (GA D W → ℂ)) : Prop :=
  ∀ f, ∃ f', (∀ g, T (κ f g) = κ f' g) ∧ ∀ F ∈ Decay θ V, T (lift κ μ 𝓕 f F) = lift κ μ 𝓕 f' F

theorem compat_id : Compat θ κ μ 𝓕 fun φ => φ := fun f => ⟨f, fun _ => rfl, fun _ _ => rfl⟩

theorem Compat.comp {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S (T φ) := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  obtain ⟨f'', c, d⟩ := hS f'
  exact ⟨f'', fun g => by simp only [a, c], fun F hF => by simp only [b F hF, d F hF]⟩

theorem Compat.add (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕)
    {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S φ + T φ := fun f => by
  obtain ⟨f', a, b⟩ := hS f
  obtain ⟨f'', c, d⟩ := hT f
  exact ⟨f' + f'', fun g => by simp only [a, c, map_add, Pi.add_apply],
    fun F hF => by simp only [b F hF, d F hF, lift_add_left hθ hκ hq hF]⟩

theorem Compat.smul (c : ℂ) {T : (GA D W → ℂ) → (GA D W → ℂ)} (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => c • T φ := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  exact ⟨c • f', fun g => by simp only [a, map_smul, Pi.smul_apply], fun F hF => by simp only [b F hF, lift_smul_left]⟩

theorem compat_sum (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {ι : Type} (s : Finset ι)
    (T : ι → (GA D W → ℂ) → (GA D W → ℂ)) (hT : ∀ i, Compat θ κ μ 𝓕 (T i)) :
    Compat θ κ μ 𝓕 fun φ => ∑ i ∈ s, T i φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (compat_id (θ := θ) (κ := κ) (μ := μ) (𝓕 := 𝓕)).smul 0
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (hT i).add hθ hκ hq ih

theorem compat_foldr (l : List ((GA D W → ℂ) → (GA D W → ℂ))) (hl : ∀ T ∈ l, Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => l.foldr (fun T acc => T acc) φ := by
  induction l with
  | nil => exact compat_id
  | cons T l ih => exact (hl T List.mem_cons_self).comp (ih fun S hS => hl S (List.mem_cons_of_mem _ hS))

theorem compat_Rder (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {X : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hX : X ∈ lieAt W τ) : Compat θ κ μ 𝓕 (Rder θ W τ X) := fun f => by
  obtain ⟨f', e⟩ := hκ.derW τ X hX f
  exact ⟨f', fun g => funext fun h => (e g h).deriv, fun F hF => funext fun h =>
    ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).2.2.2 τ X hX f f' e h).deriv⟩

theorem compat_gelf (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) (τ : D.what₂.Tau) (k : ℕ) :
    Compat θ κ μ 𝓕 (gelf θ W τ k) := by
  refine compat_sum hθ hκ hq Finset.univ _ fun idx : Fin (k + 1) → Fin W.rank =>
    compat_foldr (List.ofFn fun a : Fin (k + 1) => RderC θ W τ (Matrix.single (idx a) (idx (a + 1)) 1)) fun T hT => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hT
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem W τ (Matrix.single (idx a) (idx (a + 1)) 1)
  exact (compat_Rder hθ hκ hq h1).add hθ hκ hq ((compat_Rder hθ hκ hq h2).smul Complex.I)

theorem lift_adjoin (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {a : ℕ → Module.End ℂ M} (ha : ∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h)
    {Z : Submodule ℂ (GA D V → ℂ)} (hZ : ∀ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) {x : Module.End ℂ M}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ f, ∀ F ∈ Decay θ V ⊓ Z, ∃ F' ∈ Decay θ V ⊓ Z, lift κ μ 𝓕 (x f) F = lift κ μ 𝓕 f F' := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro f F hF
    obtain ⟨F', hF', e⟩ := GlobalTheory.T.gelfand_operator_adjoint_decaying D θ hθ V μ 𝓕 hq τ Z hZ k F hF
    refine ⟨F', hF', funext fun h => ?_⟩
    have := e _ (isMod_ker hθ hκ f h)
    rw [ha] at this
    exact this
  | algebraMap r =>
    intro f F hF
    exact ⟨r • F, Submodule.smul_mem _ r hF, by rw [Module.algebraMap_end_apply, lift_smul_left, lift_smul_right]⟩
  | add x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx f F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F hF
    exact ⟨F₁ + F₂, add_mem h₁ h₂, by
      rw [LinearMap.add_apply, lift_add_left hθ hκ hq hF.1, lift_add_right hθ hκ hq h₁.1 h₂.1, e₁, e₂]⟩
  | mul x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx (y f) F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F₁ h₁
    exact ⟨F₂, h₂, by rw [Module.End.mul_apply, e₁, e₂]⟩

theorem lift_zfin : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  rintro D θ hθ V W M _ _ κ hκ μ 𝓕 hq F hF ⟨Z, hfin, hFZ, hZ⟩ f
  let L : ↥(Decay θ V ⊓ Z) →ₗ[ℂ] (GA D W → ℂ) :=
    { toFun := fun F' => lift κ μ 𝓕 f F'.1
      map_add' := fun F₁ F₂ => lift_add_right hθ hκ hq F₁.2.1 F₂.2.1 f
      map_smul' := fun c F' => lift_smul_right c F'.1 f }
  refine ⟨LinearMap.range L, inferInstance, ⟨⟨F, hF, hFZ⟩, rfl⟩, ?_⟩
  rintro τ k _ ⟨F₁, rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hκ.cap τ
  obtain ⟨f', e, e'⟩ := compat_gelf hθ hκ hq τ k f
  obtain ⟨F₂, h₂, e₂⟩ := lift_adjoin hθ hκ hq ha (hZ τ) (hab ▸ Algebra.subset_adjoin ⟨k, rfl⟩ : b k ∈ _) f F₁.1 F₁.2
  refine ⟨⟨F₂, h₂⟩, ?_⟩
  change lift κ μ 𝓕 f F₂ = gelf θ W τ k (lift κ μ 𝓕 f F₁.1)
  rw [e' _ F₁.2.1, ← e₂]
  funext h
  simp only [lift, ← e, hb]

end GlobalTheory.Mem.LiftFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeMarkingAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mulVec_congr {A : Type} [CommRing A] {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) A) {x y w : Fin n → A}
    (e : x - Q *ᵥ y = N • w) : P *ᵥ x - (P * Q) *ᵥ y = N • P *ᵥ w := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, e, Matrix.mulVec_smul]

theorem latW_rfl {D : D7} {W : HSp D} (L : Lt D.host.E W.rank) : latW (T := W) rfl L = L := rfl

section

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {W : HSp D}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} {h : GA D W}

theorem markAd_rfl (l : Level H) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) :
    MarkAd (T := W) rfl l ι h mk ↔ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
      finVec W (mk a) - (finHom W h).1 *ᵥ (finVec W (ι a)) = l.M • w := Iff.rfl

theorem finVec_add' (a b : Fin W.rank → D.host.E) : finVec W (a + b) = finVec W a + finVec W b :=
  GlobalTheory.AdLat.cap_fv_add D.host.F a b

theorem finVec_nsmul' (n : ℕ) (a : Fin W.rank → D.host.E) : finVec W (n • a) = n • finVec W a :=
  GlobalTheory.AdLat.cap_fv_nsmul D.host.F n a

theorem finVec_sub' (a b : Fin W.rank → D.host.E) : finVec W (a - b) = finVec W a - finVec W b :=
  funext fun _ => TensorProduct.tmul_sub _ _ _

theorem markOver_of_markAd {l l₂ : Level H} (hM : l.M ∣ l₂.M) (hI : Mfr l₂ ≤ Mfr l)
    {mk mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} (h1 : MarkAd (T := W) rfl l ι h mk)
    (h2 : MarkAd (T := W) rfl l₂ ι h mk₂) : MarkOver l l₂ (latG W h) mk mk₂ := by
  intro a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨c, hc⟩ := hM
  obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 h1 a (Submodule.smul_mono_left hI ha)
  obtain ⟨w', hw', e'⟩ := (markAd_rfl l₂ mk₂).1 h2 a ha
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w)
    ((finVec_sub' _ _).trans (GlobalTheory.AdMark.sub_congr hc e e'))
  refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W h).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
  rw [← eu]
  abel

theorem finHom_mulVec_finVec {δ : GA D W} {ga : GL (Fin W.rank) D.host.E}
    (hδ : Formalism.L2.Theta.mt W δ = (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
    (v : Fin W.rank → D.host.E) : (finHom W δ).1 *ᵥ finVec W v = finVec W (ga.1 *ᵥ v) := by
  funext i
  have hf : ∀ i j, (finHom W δ).1 i j = (1 : Af D.host.F) ⊗ₜ ga.1 i j := fun i j => by
    have he' : (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ ga.1 i j := congrFun (congrFun hδ i) j
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    rfl
  simp only [Matrix.mulVec, dotProduct, hf, finVec, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    TensorProduct.tmul_sum]

theorem mem_latGHat_mul (δ : GA D W) (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom W δ).1 *ᵥ z ∈ latGHat W (δ * h) ↔ z ∈ latGHat W h := by
  rw [(GlobalTheory.MarkCoset.latG_spec D W h).2, (GlobalTheory.MarkCoset.latG_spec D W (δ * h)).2]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  have := congrArg (fun v => ((finHom W δ)⁻¹).1 *ᵥ v) e
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.inv_mul_cancel_left] at this
  exact this

end

theorem markAd_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (h : GA D W) (L : Lt D.host.E r), latW hr L = latG W h → ∀ l : Level H, (∃ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) ∧ MarkAd hr l ι h mk) ∧ ∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) → MarkAd hr l ι h mk → IsMark l L mk ∧ (∀ mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) → MarkAd hr l ι h mk') ∧ (∀ l₂ : Level H, l.M ∣ l₂.M → Mfr l₂ ≤ Mfr l → ∀ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk₂ a ∈ L) → MarkAd hr l₂ ι h mk₂ → MarkOver l l₂ L mk mk₂) ∧ ∀ (δ : GA D W) (ga : GL (Fin r) D.host.E), Formalism.L2.Theta.mt W δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) → latW hr (mapL ga L) = latG W (δ * h) ∧ MarkAd hr l ι (δ * h) (mvMap ga mk) := by
  intro D H Dw W r hr ι hι h L hL l
  subst hr
  rw [latW_rfl] at hL
  subst hL
  obtain ⟨mk₀, hm0, ha0, -⟩ := GlobalTheory.AdMark.exists_marking D H Dw l l W _ rfl ι hι dvd_rfl le_rfl h
  rw [GlobalTheory.AdMark.latR_rfl] at hm0
  replace ha0 : MarkAd (T := W) rfl l ι h mk₀ := ha0
  refine ⟨⟨mk₀, hm0.mem, ha0⟩, fun mk hmem hmk => ⟨?_, ?_, ?_, ?_⟩⟩
  · have ho := markOver_of_markAd dvd_rfl le_rfl hmk ha0
    refine ⟨hmem, ?_, fun v hv => ?_⟩
    · rintro a ha ⟨u, hu, e⟩
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact hm0.inj a ha ⟨u + u', add_mem hu hu', by rw [e', e, smul_add]⟩
    · obtain ⟨a, ha, u, hu, e⟩ := hm0.surj v hv
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact ⟨a, ha, u' + u, add_mem hu' hu, by rw [e, e', smul_add, add_assoc]⟩
  · intro mk' hc
    refine (markAd_rfl l mk').2 fun a ha => ?_
    obtain ⟨u, hu, e⟩ := hc a ha
    obtain ⟨w, hw, e'⟩ := (markAd_rfl l mk).1 hmk a ha
    refine ⟨w + finVec W u, add_mem hw (((GlobalTheory.MarkCoset.latG_spec D W h).1 u).1 hu), ?_⟩
    rw [e, finVec_add', finVec_nsmul', smul_add, ← e']
    abel
  · intro l₂ hM hI mk₂ _ h2
    exact markOver_of_markAd hM hI hmk h2
  · intro δ ga hδ
    have hf := finHom_mulVec_finVec (δ := δ) (ga := ga) hδ
    constructor
    · rw [latW_rfl]
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).2 ?_
        change finVec W (ga.1 *ᵥ x) ∈ _
        rw [← hf, mem_latGHat_mul]
        exact ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).1 hx
      · intro hv
        have hri : ga.1 *ᵥ ((ga⁻¹).1 *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        refine ⟨(ga⁻¹).1 *ᵥ v, ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).2 ?_, hri⟩
        rw [← mem_latGHat_mul δ, hf, hri]
        exact ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).1 hv
    · refine (markAd_rfl l _).2 fun a ha => ?_
      obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 hmk a ha
      refine ⟨_, (mem_latGHat_mul δ w).2 hw, ?_⟩
      change finVec W (ga.1 *ᵥ mk a) - _ = _
      rw [← hf, map_mul, Units.val_mul]
      exact mulVec_congr _ _ e

end GlobalTheory.OneMapRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfIntStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightParam_eq_infinitesimalCharacter_of_halfInt : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  first | exact @GlobalTheory.WtComb.paramV_eq_infOf | exact GlobalTheory.WtComb.paramV_eq_infOf | (intros; apply GlobalTheory.WtComb.paramV_eq_infOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocDec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_lifts_mul_mem (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w) (θ : Dec (F := E) A ≃* GalLoc w) (hθ : Continuous θ)
    (hl : ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω)) (g : GalLoc w) (H : Subgroup (GalLoc w))
    (hH : IsOpen (H : Set (GalLoc w))) :
    ∃ (σ : Weil h) (g' : GalLoc w), Lifts ι g' (σ : G E Ω) ∧ g⁻¹ * g' ∈ H := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  set d := θ.symm g with hd
  let S : Set (Dec (F := E) A) := (fun σ => g⁻¹ * θ σ) ⁻¹' (H : Set (GalLoc w))
  have hS : IsOpen S := hH.preimage (continuous_const.mul hθ)
  have hdS : d ∈ S := by
    show g⁻¹ * θ d ∈ H
    rw [hd, MulEquiv.apply_symm_apply, inv_mul_cancel]
    exact H.one_mem
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hdt : (d : G E Ω) ∈ t := by
    rw [← hts] at hdS
    exact hdS
  have hnhds : {x : G E Ω | (d : G E Ω) * x ∈ t} ∈ nhds (1 : G E Ω) := by
    apply (continuous_mul_left (d : G E Ω)).continuousAt.preimage_mem_nhds
    simpa using ht.mem_nhds hdt
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hnhds
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  obtain ⟨τ, hτW, hτ⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h (d : G E Ω) d.2 (pb.gen : Ω)
  have hfix : (d : G E Ω)⁻¹ * τ ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : (((d : G E Ω)⁻¹ * τ : G E Ω) : Ω →ₐ[E] Ω).comp F.val = F.val := pb.algHom_ext (by
      show ((d : G E Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen
      rw [AlgEquiv.mul_apply, hτ]
      show ((d : G E Ω)⁻¹ * (d : G E Ω)) (pb.gen : Ω) = pb.gen
      simp)
    exact congrArg (fun φ : F →ₐ[E] Ω => φ ⟨x, hx⟩) e
  have hτt : τ ∈ t := by
    have := hFs hfix
    simpa using this
  let σ : Dec (F := E) A := ⟨τ, Weil_le_Dec h hτW⟩
  have hσS : σ ∈ S := by
    rw [← hts]
    exact hτt
  exact ⟨⟨τ, hτW⟩, θ σ, hl σ, hσS⟩

end GlobalTheory.LocDec

namespace GlobalTheory.LocDec

theorem eq_adjoin_of_fixing_iff (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [Algebra E K] [IsScalarTower E K Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w)
    (hι : IsLocEmb A w ι) (L : IntermediateField (w.adicCompletion E) (Kbar w))
    [FiniteDimensional (w.adicCompletion E) L]
    (hfix : ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) :
    L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  obtain ⟨θ, hθ, -, hl⟩ := decomposition_mulEquiv_galLoc E Ω A w h ι hι
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set M := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hM
  have hfx : ∀ (σ : G E Ω) (g' : GalLoc w), Lifts ι g' σ → ∀ x : K,
      (g' (ι (algebraMap K Ω x)) = ι (algebraMap K Ω x) ↔ σ (algebraMap K Ω x) = algebraMap K Ω x) :=
    fun σ g' hg x => by rw [hg]; exact ι.toRingHom.injective.eq_iff
  have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let pb := Field.powerBasisOfFiniteOfSeparable E K
  have hprim : ∀ σ : G E Ω, σ (algebraMap K Ω pb.gen) = algebraMap K Ω pb.gen →
      ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := by
    intro σ hσ x
    have e : ((σ : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E K Ω)) = IsScalarTower.toAlgHom E K Ω :=
      pb.algHom_ext (by simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ x) e
  have hopen : ∀ z : Kbar w,
      IsOpen ((IntermediateField.adjoin Kw {z}).fixingSubgroup : Set (GalLoc w)) := fun z => by
    have : FiniteDimensional Kw (IntermediateField.adjoin Kw {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    exact IntermediateField.fixingSubgroup_isOpen _
  have hmemz : ∀ (z : Kbar w) (k : GalLoc w), k ∈ (IntermediateField.adjoin Kw {z}).fixingSubgroup → k z = z :=
    fun z k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk z (IntermediateField.mem_adjoin_simple_self _ _)
  have hLopen : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := IntermediateField.fixingSubgroup_isOpen L
  have hLfix : ∀ k : GalLoc w, k ∈ L.fixingSubgroup → ∀ z ∈ L, k z = z :=
    fun k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  apply le_antisymm
  · intro z hz
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hga : g (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        (IntermediateField.subset_adjoin _ _ ⟨pb.gen, rfl⟩)
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω pb.gen)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : g' (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) := by
      rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2, hga]
    have h2 := hprim σ ((hfx σ g' hlift pb.gen).1 h1)
    have h3 := (hfix σ g' hlift).2 h2 z hz
    rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz] at h3
    exact h3
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω x)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : ∀ z ∈ L, g' z = z := fun z hz => by
      rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz, hLfix g hg z hz]
    have h2 := (hfx σ g' hlift x).2 ((hfix σ g' hlift).1 h1 x)
    rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2] at h2
    exact h2

theorem eq_adjoin_of_fixing_iff_weil : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w h ι hι L _ hfix
  exact eq_adjoin_of_fixing_iff E K Ω A w h ι hι L hfix

end GlobalTheory.LocDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embeddings_tower_compatible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  first | exact @GlobalTheory.LocalExtCompletion.exists_completion_ext | exact GlobalTheory.LocalExtCompletion.exists_completion_ext | (intros; apply GlobalTheory.LocalExtCompletion.exists_completion_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEquationsHeightSumStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_equations_height_sum : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (D : CartierDiv Z) (e : ∀ v : HeightOneSpectrum (𝓞 F), Ext v) (l : HeightOneSpectrum (𝓞 F) → {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} → ℝ), (∀ v y (yt : Sp (e v).O ⟶ Z), spMap (e v).O.subtype ≫ yt = y.1 → ∃ g : Z.functionFieldˣ, D.IsEqn (yt (IsLocalRing.closedPoint (e v).O)) g ∧ l v y = Real.log ((e v).w (valAt y.1 (g : Z.functionField)))) → ∑ᶠ z : Z, (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ v, ∑ᶠ y, l v y := by
  first | exact @GlobalTheory.TrueGeo.FinSum.main | exact GlobalTheory.TrueGeo.FinSum.main | (intros; apply GlobalTheory.TrueGeo.FinSum.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialWeylCoefficientSpaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_weylCoefficientSpace : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), Nontrivial (Formalism.L2.DIV.VV K lam) := by
  first | exact @GlobalTheory.CoeffSpace.nontrivial_VV | exact GlobalTheory.CoeffSpace.nontrivial_VV | (intros; apply GlobalTheory.CoeffSpace.nontrivial_VV <;> assumption)
end

