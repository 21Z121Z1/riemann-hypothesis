import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0013
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0012
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0999
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0963
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientFieldValuationFactsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_field_valuation_facts : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  first | exact @GlobalTheory.GalLoc.FieldAt.field_at | exact GlobalTheory.GalLoc.FieldAt.field_at | (intros; apply GlobalTheory.GalLoc.FieldAt.field_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem eigen_law_absolute {M G Γ A V P : Type*} {J : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup P] [Module ℂ P] (io : V →ₗ[ℂ] P) (hinj : Function.Injective io) (val : Submodule ℂ P)
    (hran : LinearMap.range io = val) (act : A → P → P) (ρ : A → V → V) (hact : ∀ g v, act g (io v) = io (ρ g v))
    (E : M → G → V) (mv : Γ → G → J → G) (a : Γ → A) (lam : J → ℂ)
    (hlaw : ∀ f : G → V, (∃ x, E x = f) ↔ ∀ γ h k, f (mv γ h k) = lam k • ρ (a γ) (f h)) (F : G → P) :
    (∃ x, ∀ h, io (E x h) = F h) ↔ (∀ h, F h ∈ val) ∧ ∀ γ h k, F (mv γ h k) = lam k • act (a γ) (F h) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun h => ?_, fun γ h k => ?_⟩
    · rw [← hran, ← hx]
      exact ⟨_, rfl⟩
    · rw [← hx, ← hx, (hlaw _).1 ⟨x, rfl⟩ γ h k, map_smul, hact]
  · rintro ⟨hv, hl⟩
    subst hran
    choose f hf using hv
    obtain ⟨x, hx⟩ := (hlaw f).2 fun γ h k => hinj (by rw [map_smul, ← hact, hf, hf, hl])
    exact ⟨x, fun h => by rw [hx, hf]⟩

theorem _root_.GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → Function.Injective (fockOf Y (used_of_tw H.tw) j u) ∧
  LinearMap.range (fockOf Y (used_of_tw H.tw) j u) = (baseOf Z c w j).formsC (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu
  obtain ⟨hinj, hran⟩ := UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u hu
  have hact := UpperTheory.KN.ioP_tprod_intertwines_action D X X0 Y S YS Z c w j H ι hι u hu
  have hlaw := UpperTheory.KN.automorphic_form_iff_rational_level_law D X X0 Y S YS Z c w j H ι hι
  refine ⟨?_, Submodule.ext fun F => ?_⟩
  · intro x y hxy
    have h1 : (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x) =
        (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j y) :=
      funext fun h => hinj (congrFun hxy h)
    have h2 : X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j x) =
        X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j y) := by
      have h3 := (X.char.models.HV j (Y.tupT (D.what₂.muTw w))).1 h1
      rw [h3]
    rw [extV_formOf, extV_formOf] at h2
    exact (Y.IL.jMt _ (used_of_tw H.tw) j).injective (Subtype.ext h2)
  · have key := eigen_law_absolute (X.R.ioP j (PiTensorProduct.tprod ℂ u)) hinj _ hran (fun g P => (baseOf Z c w j).act g P)
      (fun g v => (X.R.cV j).ρ g v) hact
      (fun x => (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x))
      (fun (γ : Formalism.L2.Theta.GQ (Vc D j)) (h : Bridge.Gf (Vc D j)) (k : (baseOf Z c w j).levJ (twVia Z.ρ ι)) =>
        Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j))) (fun γ => (γ : GA D (Vc D j)))
      (fun k => (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ)) hlaw F
    refine Iff.trans ?_ (key.trans (Base.mem_formsC _).symm)
    exact ⟨fun ⟨x, hx⟩ => ⟨x, fun h => congrFun hx h⟩, fun ⟨x, hx⟩ => ⟨x, funext hx⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceExp

section Alg

variable {R K E V A : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Field E] [Algebra R E]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup A] [Module ℂ A]

theorem span_one_tmul (hE : Function.Injective (algebraMap R E)) {I : Type} (v : I → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) = ⊤ := by
  have key : ∀ f : V, ((1 : E) ⊗ₜ[R] f : E ⊗[R] V) ∈
      Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) := fun f => by
    have hf : f ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
      have hqK : algebraMap R K q ≠ 0 := by simpa using hq0
      have hqE : algebraMap R E q ≠ 0 := fun h => hq0 (hE (h.trans (map_zero _).symm))
      rw [← Submodule.smul_mem_iff _ hqE, algebraMap_smul, ← TensorProduct.tmul_smul, ← algebraMap_smul K q, smul_smul,
        mul_div_cancel₀ _ hqK, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul E p]
      exact Submodule.smul_mem _ _ hx
  refine Submodule.eq_top_iff'.2 fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a f =>
    have : (a ⊗ₜ[R] f : E ⊗[R] V) = a • ((1 : E) ⊗ₜ[R] f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (key f)

theorem injective_of_indep {W : Type} [AddCommGroup W] [Module E W] {ε : E →+* ℂ} (φ : W →ₛₗ[ε] A) {I : Type} (u : I → W)
    (hu : Submodule.span E (Set.range u) = ⊤) (hi : LinearIndependent ℂ fun i => φ (u i)) : Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun y hy => ?_
  have hy' : y ∈ Submodule.span E (Set.range u) := hu ▸ Submodule.mem_top
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy'
  rw [Finsupp.sum, map_sum] at hy
  simp only [map_smulₛₗ] at hy
  have h := linearIndependent_iff'.1 hi _ _ hy
  refine Finset.sum_eq_zero fun i hi' => ?_
  have : l i = 0 := ε.injective ((h i hi').trans (map_zero _).symm)
  simp only [this, zero_smul]

theorem indep_fieldRange {e : K →+* ℂ} (g : V →ₛₗ[e] A) (hg : Function.Injective g) {I : Type} {v : I → V}
    (hv : LinearIndependent K v) : LinearIndependent e.fieldRange fun i => g (v i) := by
  refine linearIndependent_iff'.2 fun t c h i hi => ?_
  choose d hd using fun i => RingHom.mem_fieldRange.1 (c i).2
  have h1 : g (∑ i ∈ t, d i • v i) = 0 := by
    rw [map_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hd]
    rfl
  have h2 := linearIndependent_iff'.1 hv _ _ (hg (h1.trans (map_zero _).symm)) i hi
  exact Subtype.ext ((hd i).symm.trans (by rw [h2, map_zero]; rfl))

end Alg

theorem rdE_injective_lattice : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)) (T : CellTie hρ D.nexp rd) (ε : KE c w →+* ℂ) (hε : Extends ρ ε), TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  Function.Injective (rdE T hε) ∧ ∀ F : Amb D j, F ∈ (ρ.B (c.twI w) j (c.sd w)).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia ρ ε) ↔ ∃ y ∈ latT c w (j.1 + 1), rdE T hε y = F := by
  intro D c w ρ hρ j rd T ε hε hok hr
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent (FractionRing (D.ntw.Ok (c.twI w) (c.k' w)))
      (D.nexp.MtLat (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w) :
        Set (D.nexp.MtV (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w)))
    rw [D.nexp.MtLat_span] at hspan
    have hE : Function.Injective (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w)) := fun a b h =>
      ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w) (by rw [← hε.apply, ← hε.apply, h])
    refine injective_of_indep (rdE T hε) _ (span_one_tmul (K := FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) hE
      (Subtype.val : s → _) (by rw [Subtype.range_coe]; exact hspan)) ?_
    have h1 := indep_fieldRange _ (T.rdV_inj _ _ _ hok) hli
    have h2 := GlobalTheory.T.linearIndependent_complex_of_subfield_coeffLattice D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ _ _ _ (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (ρ.ek (c.twI w) (c.sd w) (c.k' w)).fieldRange (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩) _ _
      (fun a h => ((Base.mem_mtLat _ _ _ _).1 ((T.rdV_mem hok).1 (hs a.2))).2 h) h1
    simpa only [rdE_tmul, map_one, one_smul] using h2
  · obtain ⟨hg, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ (c.twI w) j (c.sd w) _ _ _ hok
    have hle : (ρ.eOk (c.twI w) (c.sd w) (c.k' w)).range ≤ ringOf ε := by
      rintro _ ⟨x, rfl⟩
      refine ⟨algebraMap _ _ x, ?_⟩
      rw [← hε.apply, IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (KE c w)]
      rfl
    have hbc := GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ hg hadm _ _ _ _ _
      (ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w)) (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (levLam_mem_eOk hr T hok) _ hle
    have hsm : ∀ (a : c.Oe w) (y : Tgt c w (j.1 + 1)), rdE T hε (a • y) = ε (algebraMap _ _ a) • rdE T hε y := fun a y => by
      rw [← algebraMap_smul (KE c w) a y, map_smulₛₗ]
    intro F
    rw [hε.twVia_eq, hbc]
    constructor
    · intro hF
      induction hF using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff _ _ _ hok x).1 hx
        refine ⟨_, Submodule.subset_span ⟨f, hf, rfl⟩, ?_⟩
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨y', hy, rfl⟩ := hy
        exact ⟨x' + y', add_mem hx hy, map_add _ _ _⟩
      | smul a x _ hx =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨_, a, rfl⟩ := a
        exact ⟨a • x', Submodule.smul_mem _ _ hx, hsm a x'⟩
    · rintro ⟨y, hy, rfl⟩
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
        exact Submodule.subset_span ((T.rdV_mem hok).1 hf)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [hsm]
        exact Submodule.smul_mem _ (⟨ε (algebraMap _ _ a), a, rfl⟩ : ringOf ε) hx

end GlobalTheory.PlaceExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingCompatAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceTup

theorem hasTuples_at_place : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  intro hDS hCW _ hP D X X0 Y S YS Z c w j H ι hι τ hτ ψ' hψ' hC
  have hC0 := X.char
  have hL : GlobalTheory.BigOn.Exp.TwConj.Laws X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) :=
    ⟨⟨hC0.lev, hC0.grp, hC0.fam, hC0.models, hC0.chain, hC0.thP⟩, X.finT, ⟨X.geo.fw⟩,
      GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC0.lev hC0.fam hC0.models hC0.thP, X.guard, X.geo.pins j,
      by
        convert X.geo.phase j X.unif using 2
        all_goals (rename_i k; rw [X.phs k]; try simp),
      GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC0.lev Z.good Z.pin (c.twI w) j (c.sd w)⟩
  exact GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension hDS hCW hP.decay hP.what₂.art hP.ray X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j
    (baseOf Z c w j) X.host hL (twVia Z.ρ ι) ψ' (Y.tupT (D.what₂.muTw w)) τ (H.tup ι hι) hC
    (GlobalTheory.PlaceFix.fix_at_place hP D X X0 Y S YS Z c w j H τ hτ).2

end GlobalTheory.PlaceTup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaEventuallyAgreesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_eventually_agrees : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PtSt hL → AllSt fun _ _ _ _ _ P x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  first | exact @GlobalTheory.EtaMem.etaJ_built | exact GlobalTheory.EtaMem.etaJ_built | (intros; apply GlobalTheory.EtaMem.etaJ_built <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipThetaTranslateHalfLevel
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem not_mem_of_coprime {a b : ℕ} (h : Nat.Coprime a b) {PP : Formalism.L2.DIV.Pl D.host.E}
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hb => by
  have h1 : IsCoprime ((a : ℤ) : 𝓞 D.host.E) ((b : ℤ) : 𝓞 D.host.E) :=
    (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 D.host.E))
  obtain ⟨u, v, huv⟩ := h1
  push_cast at huv
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem exists_flip_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀
  have hfin : {PP : Formalism.L2.DIV.Pl D.host.E | ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal}.Finite := by
    have h0 : Ideal.span {((M₀ : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM₀
    refine (Ideal.finite_factors h0).subset fun PP hPP => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hPP)
  choose zOf hzG hzOne hzFlip using fun T : Finset (Formalism.L2.DIV.Pl D.host.E) =>
    GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T M₀
  choose cOf hcOf using fun T => GlobalTheory.T.flipScalar_primePow_integral_at_levelPlaces D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀ T
  refine ⟨hfin.toFinset.powerset.image zOf, hfin.toFinset.powerset.sup cOf, ?_, ?_⟩
  · intro z hz
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hz
    exact hzG T
  intro H l₂ pd hM hc1 hc2 hbad k _ _ σ la O hla hO hconj hval hz e e₂ P he hPM he₂
  have hoddM : Odd (M₀ * pd) := hM ▸ l₂.odd
  have hoddM₀ : Odd M₀ := (Nat.odd_mul.1 hoddM).1
  have hoddpd : Odd pd := (Nat.odd_mul.1 hoddM).2
  set T₀ := P.filter fun PP => ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₀
  set T₁ := P.filter fun PP => ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₁
  set P₁ := (P \ T₀) ∪ T₀.image Formalism.L2.DIV.conjPl with hP₁
  have hT₁P₁ : T₁ ⊆ P₁ := fun PP hPP => by
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hPP
    refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h1, fun h3 => ?_⟩)
    exact not_mem_of_coprime hc1 h2 (Finset.mem_filter.1 h3).2.1
  obtain ⟨⟨eT₀, heT₀⟩, e₁, he₁⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e P T₀ he (Finset.filter_subset _ _)
  obtain ⟨⟨eT₁, heT₁⟩, e₃, he₃⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e₁ P₁ T₁ he₁ hT₁P₁
  have hT₀S : T₀ ∈ hfin.toFinset.powerset :=
    Finset.mem_powerset.2 fun PP hPP => hfin.mem_toFinset.2 (Finset.mem_filter.1 hPP).2.1
  obtain ⟨x₂, hx₂, hstep₂⟩ := hzFlip T₀ eT₀ heT₀ hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  obtain ⟨z₁, hz₁G, hz₁One, hz₁F⟩ := GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T₁ pd
  obtain ⟨x₁, hx₁, hstep₁⟩ := hz₁F eT₁ heT₁ hoddpd (Nat.Coprime.coprime_mul_left (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  have hsub := GlobalTheory.T.halfTranslates_le_levelHalfTranslates_of_dvd D H l₂ e₂ e₃ _ he₂ he₃ (fun PP hPP => by
    rcases Finset.mem_union.1 hPP with h1 | h1
    · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 h1
      rcases Finset.mem_union.1 h2 with h4 | h4
      · obtain ⟨h5, h6⟩ := Finset.mem_sdiff.1 h4
        by_contra h7
        have h8 := hPM PP h5
        rw [hM, Nat.cast_mul] at h8
        rcases PP.isPrime.mem_or_mem h8 with h9 | h9
        · exact h6 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
        · exact h3 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h4
        obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
        exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
      exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2) ψ V W ΛV ΛW f₀ l₂.M O
  have hlO : ((l : ℕ) : ℂ) ∈ O := natCast_mem O l
  have ha : (l : ℂ) ^ (hfin.toFinset.powerset.sup cOf) * flipScal χW V W T₀ M₀ x₂ ∈ O := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := cOf) hT₀S)
    rw [hd, pow_add, mul_assoc]
    exact mul_mem (pow_mem hlO _) (hcOf T₀ eT₀ x₂ heT₀ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₂ k σ la O hla hO
      hconj hval hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)))
  have hb : flipScal χW V W T₁ pd x₁ ∈ O :=
    GlobalTheory.T.flipScalar_mem_coefficientRing_auxiliaryLevel D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l pd hχ hl hc1 hc2 (Nat.Coprime.coprime_mul_left (hM ▸ hbad))
      k σ la O hla hO hconj hval T₁ eT₁ x₁ heT₁ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₁
  refine ⟨zOf T₀, Finset.mem_image_of_mem _ hT₀S, z₁, hz₁G,
    hz₁One l (fun PP hPP => not_mem_of_coprime hc2 (Finset.mem_filter.1 hPP).2.1), fun f hf => ?_⟩
  obtain ⟨F₁, hF₁, hF₁eq⟩ := hstep₂ l₂.M pd e e₁ P O hM
    (fun PP hPP => not_mem_of_coprime (Nat.Coprime.symm hc1) (Finset.mem_filter.1 hPP).2.1) he (Finset.filter_subset _ _) he₁ hz f hf
  obtain ⟨F₂, hF₂, hF₂eq⟩ := hstep₁ l₂.M M₀ e₁ e₃ P₁ O (by rw [hM, mul_comm])
    (fun PP hPP => not_mem_of_coprime hc1 (Finset.mem_filter.1 hPP).2.1) he₁ hT₁P₁ he₃ hz F₁ hF₁
  set c := hfin.toFinset.powerset.sup cOf
  refine ⟨(⟨_, mul_mem ha hb⟩ : O) • F₂, Submodule.smul_mem _ _ (hsub hF₂), fun BW Q s g => ?_⟩
  have hom : om (zOf T₀ * z₁, 1) ((⟨_, mul_mem ha hb⟩ : O) • F₂) = ((l : ℂ) ^ c) • f := by
    have e1 : ((zOf T₀ * z₁, 1) : GA D V × GA D W) = (zOf T₀, 1) * (z₁, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply, Subring.smul_def]
    change om (zOf T₀, 1) (om (z₁, 1) (((l : ℂ) ^ c * flipScal χW V W T₀ M₀ x₂ * flipScal χW V W T₁ pd x₁) • F₂)) = _
    rw [← smul_smul, map_smul, hF₂eq, ← smul_smul, map_smul, hF₁eq]
  have := GlobalTheory.T.thetaKernel_fockVector_eq_of_finite_point_move D ψ θ V W χV χW om ΛV ΛW sW f₀ hP (zOf T₀ * z₁) (mul_mem (hzG T₀) hz₁G) e e₂ l₂.M O f _ _ hf
    (Submodule.smul_mem _ _ (hsub hF₂)) hom BW Q s g
  rw [← mul_assoc] at this
  exact this

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRowThetaModuleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_row_theta_module : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  first | exact @GlobalTheory.RefTheta.main | exact GlobalTheory.RefTheta.main | (intros; apply GlobalTheory.RefTheta.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixBaseOfFixingFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fix_base_of_fixing_field : PrN → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → FixBase X.core X.R.toRealDat j τ ∧ FixDat (baseOf Z c w j) τ := by
  first | exact @GlobalTheory.PlaceFix.fix_at_place | exact GlobalTheory.PlaceFix.fix_at_place | (intros; apply GlobalTheory.PlaceFix.fix_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFiniteTypesAllStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_finite_types_all : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GoodFTAll (w.D Z) := by
  first | exact @GlobalTheory.GoodMem.goodFTAll_atMem | exact GlobalTheory.GoodMem.goodFTAll_atMem | (intros; apply GlobalTheory.GoodMem.goodFTAll_atMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLTendstoNeZeroAtOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_partialL_tendsto_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  first | (exact @GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (exact GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (intros; apply GlobalTheory.RSNonvan.tendsto_partialL_ne_zero  <;> assumption)
end

