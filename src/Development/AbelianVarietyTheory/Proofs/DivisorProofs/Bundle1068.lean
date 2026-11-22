import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPerfectFreeFiniteComplex
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLocalizedIntegersIdealInField
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpace
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory Topology

namespace GlobalTheory.JSW.MirSemi

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem whit_smul_fun (c : ℂ) (F : GA E a → ℂ) (g : GA E a) : whit (c • F) g = c * whit F g := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem whit_mul_right_fun (F : GA E a → ℂ) (g h : GA E a) : whit F (g * h) = whit (fun z => F (z * h)) g := by
  simp only [whit, whittaker, mul_assoc]

theorem continuous_heightInf : Continuous (fun y : GL (Fin a) (Cinf E) => height y) := by
  unfold height
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_coe_inv.matrix_elem i j
  exact (continuous_const.add h1.norm).add h2.norm

theorem height_pos_inf (y : GL (Fin a) (Cinf E)) : 0 < height y := by
  unfold height; positivity

theorem whit_infGL_growth {F : GA E a → ℂ} (hc : Continuous F)
    (hg : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) (g : GA E a) :
    Continuous (fun y : GL (Fin a) (Cinf E) => whit F (g * infGL E a y)) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  set K : Set (GA E a) := (fun X => uGL X * g) '' closure (vecDomain E (Pos a)) with hKdef
  have hK : IsCompact K := isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const)
  obtain ⟨C, N, hC⟩ := hg K hK
  set f : GL (Fin a) (Cinf E) → (Pos a → Ad E) → ℂ := fun y X =>
    F (uGL X * (g * infGL E a y)) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) with hfdef
  have hwf : ∀ y, whit F (g * infGL E a y) = ∫ X in vecDomain E (Pos a), f y X ∂vecMeasure E (Pos a) :=
    fun y => rfl
  have hb : ∀ y, ∀ X ∈ vecDomain E (Pos a), ‖f y X‖ ≤ C * height y ^ N := by
    intro y X hX
    simp only [hfdef]
    rw [norm_mul, Circle.norm_coe, mul_one, ← mul_assoc]
    exact hC _ ⟨X, subset_closure hX, rfl⟩ y
  have hbound : ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
    intro y
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos a)) (s := vecDomain E (Pos a))
      (C := C * height y ^ N) (f := f y) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) (hb y)
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one, ← hwf] at h
  refine ⟨?_, C, N, hbound⟩
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hfc : ∀ y, Continuous (f y) := fun y =>
    (hc.comp (continuous_uGL.mul continuous_const)).mul hchar
  haveI : FirstCountableTopology (MulOpposite (Matrix (Fin a) (Fin a) (Cinf E))) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin a) (Fin a) (Cinf E))).symm.isInducing.firstCountableTopology
  haveI : FirstCountableTopology (GL (Fin a) (Cinf E)) :=
    Units.isEmbedding_embedProduct.isInducing.firstCountableTopology
  rw [continuous_iff_continuousAt]
  intro y₀
  have hev : ∀ᶠ y in 𝓝 y₀, height y < height y₀ + 1 :=
    continuous_heightInf.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  simp only [hwf]
  refine continuousAt_of_dominated (bound := fun _ => max C 0 * (height y₀ + 1) ^ N) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun y => (hfc y).aestronglyMeasurable
  · filter_upwards [hev] with y hy
    refine ae_restrict_of_forall_mem measurableSet_vecDomain fun X hX => ?_
    calc ‖f y X‖ ≤ C * height y ^ N := hb y X hX
      _ ≤ max C 0 * height y ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (height_pos_inf y).le _)
      _ ≤ max C 0 * (height y₀ + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos_inf y).le hy.le _) (le_max_right _ _)
  · refine Filter.Eventually.of_forall fun X => ?_
    have : Continuous fun y : GL (Fin a) (Cinf E) => f y X :=
      (hc.comp (continuous_const.mul (continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL))).mul
        continuous_const
    exact this.continuousAt

end GlobalTheory.JSW.MirSemi

open GlobalTheory.JSW.MirSemi in

theorem GlobalTheory.JSW.MirSemi.whitSpace_exists : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  intro E _ _ _ m S π φ hφ
  have hreg := GlobalTheory.T.cusp_form_moderate_growth_compact E (m + 1) S π φ hφ
  let 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ) :=
    { carrier := {W | ∃ F ∈ locSpan S φ.1, GlobalTheory.JSW.whit F = W}
      add_mem' := by
        rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
        refine ⟨F + G, add_mem hF hG, funext fun g => ?_⟩
        have h := ((GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1 1 g)
        simp only [one_mul] at h
        exact h
      zero_mem' := ⟨0, zero_mem _, funext fun g => by
        simpa using whit_smul_fun (0 : ℂ) (0 : GA E (m + 1) → ℂ) g⟩
      smul_mem' := by
        rintro c _ ⟨F, hF, rfl⟩
        exact ⟨c • F, Submodule.smul_mem _ c hF, funext fun g => whit_smul_fun c F g⟩ }
  refine ⟨𝒲, ⟨φ.1, self_mem_locSpan, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩ u hu g
    exact GlobalTheory.JSW.WhitModel.whit_mul (hreg F hF).1
      (fun γ g => GlobalTheory.JSW.rspan_left π (locSpan_le_rspan hφ hF) γ g) hu g
  · rintro _ ⟨F, hF, rfl⟩ h hh
    exact ⟨_, rt_mem_locSpan hF hh, funext fun g => (whit_mul_right_fun F g h).symm⟩
  · rintro _ ⟨F, hF, rfl⟩ X _ ν _ k γ hk
    refine ⟨GlobalTheory.JSW.kerInf ν k γ F, kerInf_mem_locSpan hF ν hk, funext fun g => ?_⟩
    rw [(GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk g]
    rfl
  · rintro _ ⟨F, hF, rfl⟩ g
    exact whit_infGL_growth (hreg F hF).1 (hreg F hF).2 g
  · rintro _ ⟨F, hF, rfl⟩
    obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF
    refine ⟨U, hU, fun u hu g => ?_⟩
    rw [whit_mul_right_fun]
    congr 1
    funext z
    exact hinv u hu z
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun g => rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open GlobalTheory.LB (resG_resG resG_self homOfLinear)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.DualPull

variable {X Y : Scheme.{0}}

abbrev cutO (T W : Y.Opens) : Y.Opens := T.ι ''ᵁ T.ι ⁻¹ᵁ W

theorem cutO_le (T W : Y.Opens) : cutO T W ≤ W := T.ι.image_preimage_le W

theorem cutO_le' (T W : Y.Opens) : cutO T W ≤ T := T.ι_image_le _

theorem le_cutO {T W S : Y.Opens} (h : S ≤ T) (h' : S ≤ W) : S ≤ cutO T W := by
  rw [cutO, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf h h'

theorem cutO_mono (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) : cutO T W' ≤ cutO T W :=
  le_cutO (cutO_le' _ _) ((cutO_le _ _).trans h)

def cut (T : Y.Opens) : Y.Modules :=
  (Scheme.Modules.pushforward T.ι).obj ((structureModule Y).restrict T.ι)

def cutEquiv (T W : Y.Opens) : Γ(cut T, W) ≃+ Γ(Y, cutO T W) := AddEquiv.refl _

theorem cutEquiv_smul (T W : Y.Opens) (a : Γ(Y, W)) (s : Γ(cut T, W)) :
    cutEquiv T W (a • s) = resG Y (cutO_le T W) a * cutEquiv T W s :=
  congrArg (· * cutEquiv T W s) congr($(T.ι.app_appIso_inv W) a)

theorem cutEquiv_res (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(cut T, W)) :
    cutEquiv T W' (resM (cut T) h s) = resG Y (cutO_mono T h) (cutEquiv T W s) := rfl

variable {P : Y.Modules} {T : Y.Opens}

def toCut (l : Γ(dual P, T)) : P ⟶ cut T :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv T W).symm (dualApp l (cutO_le' T W) (resM P (cutO_le T W) s))
      map_add' s t := by simp only [map_add]
      map_smul' a s := (cutEquiv T W).injective (by
        rw [RingHom.id_apply, cutEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul]) })
    fun {W W'} h s => (cutEquiv T W').injective (by
      change dualApp l _ (resM P _ (resM P h s)) = resG Y (cutO_mono T h) (dualApp l _ (resM P _ s))
      rw [← dualApp_resM, resM_resM, resM_resM])

theorem toCut_app (l : Γ(dual P, T)) (W : Y.Opens) (s : Γ(P, W)) :
    cutEquiv T W ((toCut l).app W s) = dualApp l (cutO_le' T W) (resM P (cutO_le T W) s) := rfl

theorem toCut_injective {l l' : Γ(dual P, T)} (h : toCut l = toCut l') : l = l' :=
  dual_ext fun W hW s => by
    have := congrArg (resG Y (le_cutO hW le_rfl)) ((toCut_app l W s).symm.trans (h ▸ toCut_app l' W s))
    rwa [← dualApp_resM, ← dualApp_resM, resM_resM, resM_self] at this

def ofCut (φ : P ⟶ cut T) : Γ(dual P, T) :=
  dualMk (fun W h =>
    { toFun s := resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s))
      map_add' s t := by simp only [map_add]
      map_smul' a s := by
        rw [Scheme.Modules.Hom.app_smul, cutEquiv_smul, map_mul, resG_resG, resG_self]; rfl })
    fun W W' h h' s => by
      change resG Y _ (cutEquiv T W' (φ.app W' (resM P h' s))) = resG Y h' (resG Y _ _)
      rw [app_resM, cutEquiv_res, resG_resG, resG_resG]

theorem dualApp_ofCut (φ : P ⟶ cut T) {W : Y.Opens} (h : W ≤ T) (s : Γ(P, W)) :
    dualApp (ofCut φ) h s = resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s)) := rfl

variable (f : Y ⟶ X)

def adj {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    (Scheme.Modules.pullback f).obj F ⟶ G :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).symm ψ

theorem adj_app {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G)
    {V : X.Opens} (e : T ≤ f ⁻¹ᵁ V) (s : Γ(F, V)) :
    (adj f ψ).app T (pullbackSections f F e s) = resM G e (ψ.app V s) := by
  refine (QCoh.hom_app_res (adj f ψ) e _).trans (congrArg (resM G e) ?_)
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).apply_symm_apply ψ
  rw [Adjunction.homEquiv_unit] at this
  exact congr(($this).app V s)

theorem pull_ext {F : X.Modules} {G : Y.Modules} {φ φ' : (Scheme.Modules.pullback f).obj F ⟶ G}
    (h : ∀ (V : X.Opens) (s : Γ(F, V)), φ.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s) =
      φ'.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s)) : φ = φ' := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have e : pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s = _ := QCoh.res_self _ _ _
  exact (congrArg (φ.app _) e).symm.trans ((h V s).trans (congrArg (φ'.app _) e))

variable {F G : X.Modules} {V : X.Opens}

theorem dual_pull_ext (e : T ≤ f ⁻¹ᵁ V) {l l' : Γ(dual ((Scheme.Modules.pullback f).obj F), T)}
    (h : ∀ (W : X.Opens) (_ : W ≤ V) (S : Y.Opens) (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)),
      dualApp l hS (pullbackSections f F e' s) = dualApp l' hS (pullbackSections f F e' s)) :
    l = l' := by
  refine toCut_injective (pull_ext f fun W s => (cutEquiv T _).injective ?_)
  have e' : cutO T (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
    le_inf (cutO_le T (f ⁻¹ᵁ W)) ((cutO_le' T (f ⁻¹ᵁ W)).trans e)
  have : resM _ (cutO_le T (f ⁻¹ᵁ W)) (pullbackSections f F (le_refl (f ⁻¹ᵁ W)) s) =
      pullbackSections f F e' (resM F inf_le_left s) :=
    (QCoh.res_pullbackSections f F _ _ _).trans (QCoh.pullbackSections_res f F e' _ _).symm
  rw [toCut_app, toCut_app, this]
  exact h _ inf_le_right _ _ _ _

theorem cutO_le_inf (V W : X.Opens) : cutO (f ⁻¹ᵁ V) (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
  le_inf (cutO_le (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)) (cutO_le' (f ⁻¹ᵁ V) (f ⁻¹ᵁ W))

theorem appLE_resG {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ W) (a : Γ(X, V)) :
    f.appLE W T e (resG X h a) = f.appLE V T (e.trans (f.preimage_mono h)) a :=
  congr($(f.map_appLE e (homOfLE h).op) a)

theorem resG_appLE {S : Y.Opens} (h : S ≤ T) (e : T ≤ f ⁻¹ᵁ V) (a : Γ(X, V)) :
    resG Y h (f.appLE V T e a) = f.appLE V S (h.trans e) a :=
  congr($(f.appLE_map e (homOfLE h).op) a)

def formPush (l : Γ(dual F, V)) : F ⟶ (Scheme.Modules.pushforward f).obj (cut (f ⁻¹ᵁ V)) :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).symm (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
        (dualApp l inf_le_right (resM F inf_le_left s)))
      map_add' s t := by simp only [map_add]; rfl
      map_smul' a s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).injective (by
        refine Eq.trans ?_ (cutEquiv_smul _ _ (f.app W a) _).symm
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul, map_mul, appLE_resG]
        rfl) })
    fun {W W'} h s => (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W')).injective (by
      change f.appLE (W' ⊓ V) _ _ (dualApp l _ (resM F _ (resM F h s))) =
        resG Y (cutO_mono _ (f.preimage_mono h)) (f.appLE (W ⊓ V) _ _ (dualApp l _ (resM F _ s)))
      rw [resG_appLE, ← appLE_resG f (inf_le_inf_right V h) (cutO_le_inf f V W'), ← dualApp_resM,
        resM_resM, resM_resM])

def pullForm (l : Γ(dual F, V)) : Γ(dual ((Scheme.Modules.pullback f).obj F), f ⁻¹ᵁ V) :=
  ofCut (adj f (formPush f l))

theorem dualApp_pullForm (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (hT : T ≤ f ⁻¹ᵁ V)
    (e : T ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp (pullForm f l) hT (pullbackSections f F e s) = f.appLE W T e (dualApp l h s) := by
  rw [pullForm, dualApp_ofCut, adj_app]
  change resG Y _ (resG Y (cutO_mono _ e) (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
    (dualApp l inf_le_right (resM F inf_le_left s)))) = _
  rw [resG_appLE, resG_appLE, dualApp_resM l h, appLE_resG]

variable (F) in

def pullFormHom :
    dual F ⟶ (Scheme.Modules.pushforward f).obj (dual ((Scheme.Modules.pullback f).obj F)) :=
  homOfLinear (fun V =>
    { toFun l := pullForm f l
      map_add' l l' := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = dualApp (pullForm f l) hS _ + dualApp (pullForm f l') hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_add,
          LinearMap.add_apply, map_add]
      map_smul' a l := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = resG Y hS (f.app V a) * dualApp (pullForm f l) hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_smul,
          LinearMap.smul_apply, smul_eq_mul, map_mul, appLE_resG]
        rfl })
    fun {V V'} hV l => dual_pull_ext f le_rfl fun W h S hS e s => by
      change dualApp (pullForm f (resM _ hV l)) hS _ =
        dualApp (pullForm f l) (hS.trans (f.preimage_mono hV)) _
      rw [dualApp_pullForm f _ h, dualApp_pullForm f _ (h.trans hV), dualApp_res]

variable (F) in

def theta : (Scheme.Modules.pullback f).obj (dual F) ⟶ dual ((Scheme.Modules.pullback f).obj F) :=
  adj f (pullFormHom f F)

theorem dualApp_theta (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ V)
    {S : Y.Opens} (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp ((theta f F).app T (pullbackSections f (dual F) e l)) hS (pullbackSections f F e' s) =
      f.appLE W S e' (dualApp l h s) := by
  rw [theta, adj_app]
  exact dualApp_pullForm f l h (hS.trans e) e' s

theorem theta_naturality (φ : F ⟶ G) :
    (Scheme.Modules.pullback f).map (dualMap φ) ≫ theta f F =
      theta f G ≫ dualMap ((Scheme.Modules.pullback f).map φ) :=
  pull_ext f fun V l => dual_pull_ext f le_rfl fun W h S hS e s => by
    change dualApp ((theta f F).app _ (((Scheme.Modules.pullback f).map (dualMap φ)).app _ _)) hS _ =
      dualApp ((theta f G).app _ _) hS (((Scheme.Modules.pullback f).map φ).app _ _)
    rw [QCoh.pullback_map_app_pullbackSections, QCoh.pullback_map_app_pullbackSections,
      dualApp_theta f _ h, dualApp_theta f _ h, dualApp_dualMap]

theorem isIso_theta {r : ℕ} (h : IsVB F r) : IsIso (theta f F) := by
  have := h.isQuasicoherent
  have := h.dual.isQuasicoherent
  refine isIso_of_frames (ι := Fin r) _ fun y => ?_
  obtain ⟨U, e, hx, he⟩ := h (f y)
  refine ⟨f ⁻¹ᵁ U, _, hx, he.dual.pullback f, ?_⟩
  have H (i : Fin r) : (theta f F).app _ (pullbackSections f (dual F) (le_refl (f ⁻¹ᵁ U))
      (he.coord i)) = (he.pullback f).coord i :=
    dual_pull_ext f le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta f _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact (he.pullback_basis_repr f hW e' s i).symm
  rw [funext H]
  exact (he.pullback f).dual

theorem exists_dual_pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X), ∃ θ : ∀ F : X.Modules, (Scheme.Modules.pullback f).obj (dual F) ⟶ dual ((Scheme.Modules.pullback f).obj F), (∀ (F G : X.Modules) (φ : F ⟶ G), (Scheme.Modules.pullback f).map (dualMap φ) ≫ θ F = θ G ≫ dualMap ((Scheme.Modules.pullback f).map φ)) ∧ (∀ (F : X.Modules) (V : X.Opens) (T : Y.Opens) (e : T ≤ f ⁻¹ᵁ V) (l : Γ(dual F, V)) (s : Γ(F, V)), dualApp ((θ F).app T (GlobalTheory.QCoh.pullbackSections f (dual F) e l)) le_rfl (GlobalTheory.QCoh.pullbackSections f F e s) = f.appLE V T e (dualApp l le_rfl s)) ∧ ∀ (F : X.Modules) (r : ℕ), IsVB F r → IsIso (θ F) :=
  fun _ _ f => ⟨theta f, fun _ _ φ => theta_naturality f φ,
    fun _ _ _ e l s => dualApp_theta f l le_rfl e le_rfl e s, fun _ _ h => isIso_theta f h⟩

end GlobalTheory.DualPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.FinIsoExists

theorem exists_isometry {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (σ : A →+* A) {n n' : ℕ} (h : n = n')
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n') (Fin n') A) (β : GL (Fin n) A) (β' : GL (Fin n') A)
    (u : GL (Fin n) R) (u' : GL (Fin n') R)
    (hu : Formalism.UG.cT σ (β * Formalism.UG.bc φ u).val * J * (β * Formalism.UG.bc φ u).val = 1)
    (hu' : Formalism.UG.cT σ (β' * Formalism.UG.bc φ u').val * J' * (β' * Formalism.UG.bc φ u').val = 1) :
    ∃ u₀ : GL (Fin n') R, ∀ y : GL (Fin n') R, β' * Formalism.UG.bc φ y * β'⁻¹ ∈ Formalism.UG.UJ σ J' →
      ∃ (j : Matrix (Fin n') (Fin n) A) (j' : Matrix (Fin n) (Fin n') A), j * j' = 1 ∧ j' * j = 1 ∧
        Formalism.UG.cT σ j * J' * j = J ∧ j * β.val = (β' * Formalism.UG.bc φ (y * u₀)).val.submatrix id (Fin.cast h) := by
  subst h
  refine ⟨u' * u⁻¹, fun y hy => ?_⟩
  set k := β' * Formalism.UG.bc φ y * β'⁻¹ with hk
  set B := β * Formalism.UG.bc φ u with hB
  set B' := β' * Formalism.UG.bc φ u' with hB'
  have hy' : Formalism.UG.cT σ k.val * J' * k.val = J' := hy
  refine ⟨(k * B' * B⁻¹).val, (k * B' * B⁻¹)⁻¹.val, Units.mul_inv _, Units.inv_mul _, ?_, ?_⟩
  · calc Formalism.UG.cT σ (k * B' * B⁻¹).val * J' * (k * B' * B⁻¹).val
        = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B'.val * (Formalism.UG.cT σ k.val * J' * k.val) * B'.val) * B⁻¹.val := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B.val * J * B.val) * B⁻¹.val := by rw [hy', hu, hu']
      _ = Formalism.UG.cT σ (B.val * B⁻¹.val) * J * (B.val * B⁻¹.val) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · have e : k * B' * B⁻¹ * β = β' * Formalism.UG.bc φ (y * (u' * u⁻¹)) := by
      rw [hk, hB, hB', map_mul, map_mul, map_inv]
      group
    rw [← Units.val_mul, e]
    rfl

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := by
    rw [mem_blockTri]
    intro i j hij
    simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr hg]
  rfl

theorem exists_isFinIso : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)), V.rank = V'.rank → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP') → ∃ j Φ, IsFinIso V V' β β' Pg j Φ := by
  intro D V V' β Λ N β' Λ' N' Pg h hβ hβ' hPg
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V β Λ N hβ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V' β' Λ' N' hβ'
  obtain ⟨u₀, hu₀⟩ := exists_isometry (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h _ _ β β' u u' hu hu'
  have hL := GlobalTheory.T.finite_group_lifts_to_parahoric_level V' β' (datW V'.rank Pg (LevelP.triv Pg V'.rank ℂ) Frm.B) Λ' N' hβ' rfl hPg
  obtain ⟨κ, -, hκ, hred⟩ := hL (fun PP => (Formalism.UG.bc (resS D.host.F PP.1) u₀)⁻¹)
  obtain ⟨y, hy⟩ := parLev_St hκ
  have hU : β' * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype y * β'⁻¹ ∈
      UA D.sp.cm V'.gram := by
    have h1 := parLev_UA hκ
    rw [← hy] at h1
    exact h1
  obtain ⟨j, j', h1, h2, h3, h4⟩ := hu₀ y hU
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso V V' j j' h1 h2 h3
  refine ⟨j, Φ, h3, hΦ, h, y * u₀, h4, fun PP hPP => ?_⟩
  have h5 : upperLeftBlock le_rfl (redFn β' PP (finE V' κ)) = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ := congrFun hred ⟨PP, hPP⟩
  have h6 : redFn β' PP (finE V' κ) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (redFn β' PP) hy).symm.trans (redFn_frGL β' PP y)
  have h7 : Formalism.UG.bc (resS D.host.F PP) y = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ :=
    h6.symm.trans ((restrictedBlock_self_apply _ _).symm.trans h5)
  exact (map_mul _ y u₀).trans (mul_eq_one_iff_eq_inv.2 h7)

end GlobalTheory.FinIsoExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexPrimitiveLineBundleCechFibresStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_free_complex_primitive_lineBundle_cech_fibres : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ F : LB B.left, F.IsLB → (∃ u : LB.Gen (abelian₂ B F), u.IsGen) → ∀ P : Perf B.hom F, ∃ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] ((Fin P.a → A) ⧸ LinearMap.range P.D₀.transpose.mulVecLin)) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ i, (g < i ∨ ¬ Triv (F.pull π)) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (K : Type) [Field K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K] (cechLB f' (F.pull π) D).homology i) := by
  first | exact @GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech | exact GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech | (intros; apply GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLocalizedIntegersIdealInFieldStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_localized_integers_ideal_in_field : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ) (K : Set L), 0 ∈ K →
    (∀ a ∈ K, ∀ b ∈ K, a + b ∈ K) →
    (∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K) →
    (∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a)) →
    ∃ g ∈ K, ∀ a ∈ K, ∃ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) ∧ a = c * g := by
  first | (exact @GlobalTheory.LocIntPrincipal.exists_generator) | (exact GlobalTheory.LocIntPrincipal.exists_generator) | (intros; apply GlobalTheory.LocIntPrincipal.exists_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentCutoffTendstoAdelicUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotentCutoff_tendsto_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  first | exact @GlobalTheory.UnitaryCutoff.exists_approx | exact GlobalTheory.UnitaryCutoff.exists_approx | (intros; apply GlobalTheory.UnitaryCutoff.exists_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulIsAdicIntegralInTensorBasisStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_smul_isAdicIntegralInTensorBasis : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  first | (exact @GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (exact GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_int_smul_isIntB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerDenominatorNotMemOfValuationLeOneStatement
section
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_denominator_not_mem_of_valuation_le_one : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  first | exact @GlobalTheory.IntegralDenom.exists_denom_not_mem | exact GlobalTheory.IntegralDenom.exists_denom_not_mem | (intros; apply GlobalTheory.IntegralDenom.exists_denom_not_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumConjClasses
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_conj_classes : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  first | (exact @GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (exact GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (intros; apply GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer  <;> assumption)
end

