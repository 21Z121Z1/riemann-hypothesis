import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.PullPull

section Sections

variable {X Y Z : Scheme.{0}}

theorem pullbackId_hom_app (E : X.Modules) {U V : X.Opens} (h : U ≤ (𝟙 X) ⁻¹ᵁ V) (h' : U ≤ V)
    (s : Γ(E, V)) :
    ((Scheme.Modules.pullbackId X).hom.app E).app U (pullbackSections (𝟙 X) E h s) =
      resM E h' s := by
  have e := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)) (Scheme.Modules.pullbackId X).hom E
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at e
  refine (app_resM _ h _).trans ?_
  exact congrArg (resM _ h') congr(($e).app V s).symm

theorem pullbackComp_hom_app (b : Z ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : Z.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h s]
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a).hom.app E = 𝟙 _ := by simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

end Sections

section Met

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E E' : X.Modules} {r : ℕ}

theorem eq_map_of_frames {h : Met p σ E r} {h' : Met p σ E' r} (φ : E ≅ E')
    (H : ∀ y, ∃ c : Chart E r, y ∈ ptsIn p σ c.U ∧ h'.G (c.map φ) y = h.G c y) : h' = h.map φ :=
  Met.ext_of_exists fun y => by
    obtain ⟨c, hc, e⟩ := H y
    exact ⟨c.map φ, hc, by rw [e, h.map_G φ c hc]⟩

theorem eq_map_pull_id (h : Met p σ E r) :
    h = (h.pull (𝟙 X) (Category.id_comp p)).map ((Scheme.Modules.pullbackId X).app E) := by
  refine eq_map_of_frames _ fun y => ?_
  obtain ⟨c, hc⟩ : ∃ c : Chart E r, PtsOver.map (𝟙 X) (Category.id_comp p) _ y ∈ ptsIn p σ c.U :=
    ⟨_, h.isVB.mem_pick _⟩
  refine ⟨Chart.pull c h.isVB (𝟙 X), hc, ?_⟩
  rw [h.pull_G _ _ _ hc, PtsOver.map_id]
  rw [PtsOver.map_id] at hc
  have hl : (𝟙 X) ⁻¹ᵁ c.U ≤ c.U := fun _ h => h
  have e (a : Fin r) : (Chart.map (Chart.pull c h.isVB (𝟙 X))
      ((Scheme.Modules.pullbackId X).app E)).e a = resM E hl (c.e a) :=
    pullbackId_hom_app E _ hl _
  ext a b
  rw [← h.form_frame (Chart.map (Chart.pull c h.isVB (𝟙 X))
    ((Scheme.Modules.pullbackId X).app E)) hc a b, ← h.form_frame c hc a b, e, e]
  exact h.form_resM _ _ hl hc

theorem pull_comp_eq_map (h : Met p σ E r) {q : Y ⟶ Sp k} {t : Z ⟶ Sp k} (π : Y ⟶ X) (τ : Z ⟶ Y)
    (hπ : π ≫ p = q) (hτ : τ ≫ q = t) (e : (τ ≫ π) ≫ p = t) :
    h.pull (τ ≫ π) e =
      ((h.pull π hπ).pull τ hτ).map ((Scheme.Modules.pullbackComp τ π).app E) := by
  refine eq_map_of_frames _ fun z => ?_
  obtain ⟨c, hc⟩ : ∃ c : Chart E r, PtsOver.map (τ ≫ π) e _ z ∈ ptsIn p σ c.U :=
    ⟨_, h.isVB.mem_pick _⟩
  have hc' : PtsOver.map π hπ _ (PtsOver.map τ hτ _ z) ∈ ptsIn p σ c.U := by
    rw [PtsOver.map_map]; exact hc
  refine ⟨Chart.pull (Chart.pull c h.isVB π) (h.pull π hπ).isVB τ, hc', ?_⟩
  have g₁ := (h.pull π hπ).pull_G τ hτ (Chart.pull c h.isVB π) hc'
  have g₂ := h.pull_G π hπ c hc'
  have g₃ : h.G c (PtsOver.map π hπ _ (PtsOver.map τ hτ _ z)) =
      h.G c (PtsOver.map (τ ≫ π) e _ z) := congrArg _ (PtsOver.map_map _ _ _ _ _ _)
  refine Eq.trans ?_ (g₁.trans (g₂.trans g₃)).symm
  have hT : τ ⁻¹ᵁ π ⁻¹ᵁ c.U ≤ (τ ≫ π) ⁻¹ᵁ c.U := fun _ h => h
  have f (a : Fin r) : (Chart.map (Chart.pull (Chart.pull c h.isVB π) (h.pull π hπ).isVB τ)
      ((Scheme.Modules.pullbackComp τ π).app E)).e a =
      pullbackSections (τ ≫ π) E hT (c.e a) :=
    pullbackComp_hom_app τ π E le_rfl le_rfl hT _
  refine Matrix.ext fun a b => ?_
  refine ((h.pull (τ ≫ π) e).form_frame (Chart.map (Chart.pull (Chart.pull c h.isVB π)
    (h.pull π hπ).isVB τ) ((Scheme.Modules.pullbackComp τ π).app E)) hc a b).symm.trans ?_
  refine Eq.trans ?_ (h.form_frame c hc a b)
  refine Eq.trans (congrArg₂ (fun s t => (h.pull (τ ≫ π) e).form s t z) (f a) (f b)) ?_
  exact h.form_pull (τ ≫ π) e _ _ hT hc

end Met

end GlobalTheory.PullPull

namespace GlobalTheory.VMetric

theorem isIsometry_pull_id_comp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r), (h.pull (𝟙 X) (Category.id_comp p)).IsIsometry h ((Scheme.Modules.pullbackId X).app E) ∧ ∀ (Y Z : Scheme.{0}) (q : Y ⟶ Sp k) (t : Z ⟶ Sp k) (π : Y ⟶ X) (τ : Z ⟶ Y) (hπ : π ≫ p = q) (hτ : τ ≫ q = t) (e : (τ ≫ π) ≫ p = t), ((h.pull π hπ).pull τ hτ).IsIsometry (h.pull (τ ≫ π) e) ((Scheme.Modules.pullbackComp τ π).app E) := by
  intro k _ X p E r h
  refine ⟨isIsometry_iff _ |>.2 (VMetric.ext (funext fun σ => PullPull.eq_map_pull_id (h.met σ))), ?_⟩
  intro Y Z q t π τ hπ hτ e
  exact isIsometry_iff _ |>.2 (VMetric.ext (funext fun σ =>
    PullPull.pull_comp_eq_map (h.met σ) π τ hπ hτ e))

end GlobalTheory.VMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem symp_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JB JA xᵀ yᵀ = GlobalTheory.WeilM.symp c ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable [Invertible (2 : R)]

def transD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', d.form]
    rfl

variable {c}

theorem transD_e {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α β E) : (transD c d).e xᵀ = d.e x := by
  simp [transD]

theorem transD_rho {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (ψ : AddChar R ℂ) (w : Matrix β α E) :
    (transD c d).rho ψ w = d.rho ψ wᵀ := by
  simp [GlobalTheory.WeilM.Darboux.rho, transD]

variable [TopologicalSpace R] [TopologicalSpace E] {C : GlobalTheory.WeilM.TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ] {d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ}
  {om : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB →* Module.End ℂ ((κ → R) → ℂ)}

theorem isUSplitting_inr (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inr _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inr _ _) (continuous_const.prodMk continuous_id)⟩
  have := h.impl (1, g) w φ hφ
  simpa [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB] using this

theorem isUSplitting_inl (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ (transD c d) (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inl _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inl _ _) (continuous_id.prodMk continuous_const)⟩
  have := h.impl (g, 1) wᵀ φ hφ
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, transD_rho]
  convert this using 2
  simp [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, Matrix.transpose_mul]

end Gen

section Theta

variable (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)]

def thetaTr {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : W → ℂ :=
  fun w => GlobalTheory.WeilM.thetaSum F (d.rho ψ w Φ)

end Theta

section Transport

def IsTransport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {ξ : AE D}
    {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ))
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)) :
    Prop :=
  ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T),
    mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om (a, b) Φ ∈ GlobalTheory.WeilM.schA D.host.F κ ∧
      thetaTr D.host.F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr D.host.F co ψ Φ)

end Transport

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricCombUnitOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.ArInt GlobalTheory.Cartier

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsIntegral X] [IsLocallyNoetherian X] in

theorem isometric_comb_unit_one (M : HermLB p) :
    (comb (fun _ : Unit => M) fun _ => 1).Isometric M := by
  have e : (fun _ : Unit => (1 : ℤ)) = Pi.single () 1 := by
    funext u
    simp
  rw [e]
  exact isometric_comb_single (fun _ : Unit => M) ()

theorem arMix_pair (HM : Published.ArMix) (hX : IsArithVar p 1) {L M : HermLB p}
    {Φ : MvPolynomial (Option Unit) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option Unit => o.elim L fun _ => M) 1 Φ) {h : X → ℝ} (H : M.IsArithHeight h)
    (r : L.B.ι → X.functionFieldˣ) (hr : IsRatSec L.B r) :
    M.ArchIntegrable L 1 hr ∧
      Φ (MvPolynomial.X none * MvPolynomial.X (some ())) =
        ∑ᶠ z, ((L.div hr).mult z : ℝ) * h z - M.archInt L 1 hr := by
  have e := isometric_comb_unit_one M
  obtain ⟨h₁, h₂⟩ := HM k X p 1 hX Unit L (fun _ => M) Φ hΦ (fun _ => 1) h
    (e.symm.isArithHeight hX H) r hr
  have hl : MvPolynomial.rename some (lin fun _ : Unit => (((1 : ℤ) : ℤ) : ℝ)) ^ 1 =
      (MvPolynomial.X (some ()) : MvPolynomial (Option Unit) ℝ) := by
    simp [lin]
  rw [hl] at h₂
  refine ⟨fun σ => ?_, ?_⟩
  · rw [← e.chernIntegrableOn_eq σ 1]
    exact h₁ σ
  · have a : (comb (fun _ : Unit => M) fun _ => 1).archInt L 1 hr = M.archInt L 1 hr :=
      finsum_congr fun σ => congrFun (congrFun (e.chernInt_eq σ 1) _) _
    rw [h₂, a]

theorem isInter_iff (HE : Published.ArExists) (HM : Published.ArMix) (hX : IsArithVar p 1) {L M : HermLB p}
    {Φ : MvPolynomial (Option Unit) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option Unit => o.elim L fun _ => M) 1 Φ) (a : ℝ) :
    L.IsInter M a ↔ a = Φ (MvPolynomial.X none * MvPolynomial.X (some ())) := by
  constructor
  · rintro ⟨h, H, ha⟩
    obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
    rw [(ha r hr).2, (arMix_pair HM hX hΦ H r hr).2]
  · rintro rfl
    obtain ⟨h, H⟩ := (HE k X p 1 hX).1 M
    exact ⟨h, H, fun r hr => arMix_pair HM hX hΦ H r hr⟩

theorem isInter_of_comb (HE : Published.ArExists) (HM : Published.ArMix) (HI : Published.ArIso) (hX : IsArithVar p 1)
    {ι : Type} [Fintype ι] {T : ι → HermLB p} {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΨ : IsArFun T 1 Ψ)
    {u v : ι → ℤ} {L M : HermLB p} (hu : (comb T u).Isometric L) (hv : (comb T v).Isometric M) :
    L.IsInter M (Ψ (lin (fun i => (u i : ℝ)) * lin fun i => (v i : ℝ))) := by
  have hΦ := ((HI k X p 1 hX).2 ι T Ψ hΨ).2.2 (Option Unit) (fun o => o.elim L fun _ => M)
    (fun o => o.elim u fun _ => v) (by rintro (_ | _); exacts [hu, hv])
  refine (isInter_iff HE HM hX hΦ _).2 ?_
  simp

theorem lin_add_int {ι : Type} [Fintype ι] (u v : ι → ℤ) :
    (lin fun i => (((u + v) i : ℤ) : ℝ)) = (lin fun i => (u i : ℝ)) + lin fun i => (v i : ℝ) := by
  simp [lin, add_mul, Finset.sum_add_distrib]

end GlobalTheory.HermLB

namespace GlobalTheory

theorem isInter_calculus : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X]
    [IsLocallyNoetherian X], IsArithVar p 1 → ∀ (L L' M : HermLB p), (∃ a, L.IsInter M a) ∧
      (∀ a, L.IsInter M a → M.IsInter L a) ∧
      (∀ a a', L.IsInter M a → L'.IsInter M a' → (L.tens L').IsInter M (a + a')) ∧
      ∀ a x y z, L.IsInter M a → L.IsSelfInter x → M.IsSelfInter y → (L.tens M).IsSelfInter z →
        z = x + 2 * a + y := by
  intro hC k _ X p _ _ hX L L' M
  have HE := hC.arExists
  have HM := hC.arMix
  have HI := hC.arIso
  let T : Fin 3 → HermLB p := ![L, L', M]
  obtain ⟨Ψ, hΨ⟩ := ((HE k X p 1 hX).2 (Fin 3) T).1
  let e : Fin 3 → Fin 3 → ℤ := fun i => Pi.single i 1
  have c₀ : (comb T (e 0)).Isometric L := isometric_comb_single T 0
  have c₁ : (comb T (e 1)).Isometric L' := isometric_comb_single T 1
  have c₂ : (comb T (e 2)).Isometric M := isometric_comb_single T 2
  have l (i : Fin 3) : (lin fun j => ((e i j : ℤ) : ℝ)) = MvPolynomial.X i := lin_single i
  have s₀₁ : (comb T (e 0 + e 1)).Isometric (L.tens L') :=
    (isometric_comb_add T _ _).trans (c₀.tens c₁)
  have s₀₂ : (comb T (e 0 + e 2)).Isometric (L.tens M) :=
    (isometric_comb_add T _ _).trans (c₀.tens c₂)
  have I₀ := HermLB.isInter_of_comb HE HM HI hX hΨ c₀ c₂
  have I₀' := HermLB.isInter_of_comb HE HM HI hX hΨ c₂ c₀
  have I₁ := HermLB.isInter_of_comb HE HM HI hX hΨ c₁ c₂
  have I₀₁ := HermLB.isInter_of_comb HE HM HI hX hΨ s₀₁ c₂
  rw [l, l] at I₀ I₀' I₁
  rw [HermLB.lin_add_int, l, l, l] at I₀₁
  refine ⟨⟨_, I₀⟩, fun a ha => ?_, fun a a' ha ha' => ?_, fun a x y z ha hx hy hz => ?_⟩
  · rw [ha.unique hX I₀, mul_comm]
    exact I₀'
  · rw [ha.unique hX I₀, ha'.unique hX I₁, ← map_add, ← add_mul]
    exact I₀₁
  · have S₀ := c₀.isSelfInter hX (hΨ.1 (e 0))
    have S₂ := c₂.isSelfInter hX (hΨ.1 (e 2))
    have S := s₀₂.isSelfInter hX (hΨ.1 (e 0 + e 2))
    rw [l] at S₀ S₂
    rw [HermLB.lin_add_int, l, l] at S
    rw [hx.unique hX S₀, hy.unique hX S₂, hz.unique hX S, ha.unique hX I₀]
    have E : (MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ) ^ (1 + 1) =
        MvPolynomial.X 0 ^ (1 + 1) + (MvPolynomial.X 0 * MvPolynomial.X 2 + MvPolynomial.X 0 * MvPolynomial.X 2) +
          MvPolynomial.X 2 ^ (1 + 1) := by ring
    rw [E, map_add, map_add, map_add]
    ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocal
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

open IsDedekindDomain

namespace GlobalTheory.InertIwasawaUnram

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ hσ hU n J hJ x y hx hy L hL v hv hSD g
  haveI := hL
  obtain ⟨c, hc⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hσ inferInstance
  have hram : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.ramificationIdx (𝓞 F) = 1 := fun P => by
    haveI := P.isPrime
    haveI : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := inferInstance
    exact Ideal.ramificationIdx_eq_one _ _
  have hUn : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v := fun P _ => hram P
  have hIU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := fun P _ => hram P
  obtain ⟨w, hw⟩ := ((GlobalTheory.LFun.exists_isInertChart σ hσ v).1 hIU).resolve_left hv
  obtain ⟨q, k, hk, hg, β, hβ⟩ := GlobalTheory.InertIwasawaLoc.exists_loc hσ hc hJ hw hUn hSD
    (e := x) (p := cT (σ : E →+* E) y * J) (by rw [Matrix.mul_assoc] at hy ⊢; exact hy) hx g
  exact ⟨q, k, hk, hg, β, hβ⟩

end GlobalTheory.InertIwasawaUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

namespace GlobalTheory.RigidTranslate

open GlobalTheory.PolTranslate ReciprocityTheory.ChartRestriction.G.DVR

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem toUnit_inv_mul_self (a : 𝟙_ (Over S) ⟶ A) (T : Over S) :
    (toUnit T ≫ a⁻¹) * (toUnit T ≫ a) = 1 := by
  rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one]

theorem transl_inv_comp_transl (a : 𝟙_ (Over S) ⟶ A) : transl a⁻¹ ≫ transl a = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]

theorem kTriv_pull_transl (x : 𝟙_ (Over S) ⟶ A) {L : LB A.left} (hL : L.IsLB) (h : Out.KTriv A L) :
    Out.KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x⁻¹).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x⁻¹))) V
  have k₂ : T ◁ transl x⁻¹ ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_inv_comp_transl, Category.comp_id]
  have k₃ : T ◁ transl x⁻¹ ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

end

theorem kTriv_rigTransl_any : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro S A _ L hL a h R _ s y hy
  refine kTriv_pull_transl a hL h R s y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, gen_of_lbIso (pull_isLB (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) _)
    (pull_isLB (DVR.linComb_isLB _ (pull_isLB hL _) _ _) _)
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_diff_diff hL _ _ _ _ ?_)) c hc⟩
  rw [comp_const, comp_const]

end GlobalTheory.RigidTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullCompOfEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel

theorem lbIso_pull_comp_of_eq {X X₁ X₂ : Scheme.{0}} {M : LB X} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X} {φ : X₂ ⟶ X₁}
    (hφ : π₂ = φ ≫ π₁) {L₁ : LB X₁} (e : LBIso L₁ (M.pull π₁)) : LBIso (M.pull π₂) (L₁.pull φ) :=
  LBIso.chartPull (chartPullSame M (fun _ : PUnit => π₂) (fun _ => π₁) (fun _ => 1) φ fun _ => hφ)
    (Geo.Tor.chartPullPull L₁ φ φ rfl) e.symm

theorem objMap_cancel : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (T X Y : Scheme.{0}) (t : T ⟶ Sp (D.OEp p)) (sX : X ⟶ Sp (D.OEp p)) (sY : Y ⟶ Sp (D.OEp p))
    (o : GlobalTheory.UPel.Obj D p N t) (o₁ : GlobalTheory.UPel.Obj D p N sX) (u : GlobalTheory.UPel.Obj D p N sY) (x : T ⟶ X) (π : X ⟶ Y),
    GlobalTheory.UPel.ObjMap o₁ u π → GlobalTheory.UPel.ObjMap o u (x ≫ π) → Nonempty (GlobalTheory.UPel.ObjMap o o₁ x) := by
  intro F _ _ _ D p N T X Y t sX sY o o₁ u x π m₁ m
  have w : m.φ ≫ u.A.hom = (o.A.hom ≫ x) ≫ π := by rw [m.cart.1.w, Category.assoc]
  let φ := m₁.cart.1.lift m.φ (o.A.hom ≫ x) w
  have hφ : φ ≫ m₁.φ = m.φ := m₁.cart.1.lift_fst _ _ _
  have hφ2 : φ ≫ o₁.A.hom = o.A.hom ≫ x := m₁.cart.1.lift_snd _ _ _
  refine ⟨{ φ := φ, cart := ?_, act := ?_, pol := ?_, eta := ?_ }⟩
  · exact IsGrpPullback.cancel m₁.cart (m.cart.congr rfl hφ.symm) hφ2
  · intro a
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₁.act, ← Category.assoc, hφ]
    · rw [Category.assoc, Category.assoc, Over.w (o₁.act.act a), hφ2, ← Category.assoc, Over.w (o.act.act a)]
  · exact LBIso.trans o.PP.isLB (pull_isLB u.PP.isLB _) (pull_isLB o₁.PP.isLB φ) m.pol
      (lbIso_pull_comp_of_eq hφ.symm m₁.pol)
  · intro a
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₁.eta]
    · rw [Category.assoc, hφ2, ← Category.assoc, Over.w (o.eta a), Category.assoc, Over.w (o₁.eta a)]
      simp

end GlobalTheory.UPel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChartStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normFactor_and_density_near_one_in_flagChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧ Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  first | exact @GlobalTheory.ChartNearOne.chart_near_one | exact GlobalTheory.ChartNearOne.chart_near_one | (intros; apply GlobalTheory.ChartNearOne.chart_near_one <;> assumption)
end

