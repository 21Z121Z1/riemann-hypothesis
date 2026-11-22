import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatricesInvariantSupportedEqSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SBClosure

open scoped Topology

theorem nonarch_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup (G i)),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

theorem eq_smul_indicator_closure {X : Type} [AddCommGroup X] [TopologicalSpace X] [NonarchimedeanAddGroup X]
    (S : AddSubgroup X) (B : Set X) (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hf0 : f ≠ 0) (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB X, (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) → ∃ c : ℂ, g = c • f) :
    ∃ c : ℂ, f = c • (closure (S : Set X)).indicator 1 ∧ IsOpen (closure (S : Set X)) ∧
      IsCompact (closure (S : Set X)) := by
  set H : AddSubgroup X := S.topologicalClosure with hHdef
  have hHc : (H : Set X) = closure (S : Set X) := rfl
  rw [← hHc]
  have hcont : Continuous f := hf.1.continuous
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (funext h)
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ GlobalTheory.WeilM.SB X, U.indicator φ ∈ GlobalTheory.WeilM.SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hSH : S ≤ H := S.le_topologicalClosure
  have hHcl : IsClosed (H : Set X) := S.isClosed_topologicalClosure
  have hH : ∀ h ∈ H, f (Y₀ + h) = f Y₀ := by
    intro h hh
    have hcl : IsClosed {h : X | f (Y₀ + h) = f Y₀} :=
      isClosed_eq (hcont.comp (continuous_const.add continuous_id)) continuous_const
    have hS : (S : Set X) ⊆ {h : X | f (Y₀ + h) = f Y₀} := fun s hs => hinv s hs Y₀
    exact (closure_minimal hS hcl) hh
  have hW : ∀ x, f x ≠ 0 → x - Y₀ ∈ H := by
    intro x hx
    by_contra hxH
    have hopen : (H : Set X)ᶜ ∈ 𝓝 (x - Y₀) := hHcl.isOpen_compl.mem_nhds hxH
    have h0 : (fun u => x - Y₀ + u) ⁻¹' (H : Set X)ᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      simpa using hopen
    obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    set V : AddSubgroup X := H ⊔ U.toAddSubgroup with hVdef
    have hVo : IsOpen (V : Set X) := AddSubgroup.isOpen_mono (le_sup_right : U.toAddSubgroup ≤ V) U.isOpen
    have hVc : IsClosed (V : Set X) := AddSubgroup.isClosed_of_isOpen V hVo
    have hxV : x - Y₀ ∉ V := by
      intro hm
      obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hm
      have hb' : -b ∈ U := U.neg_mem hb
      have := hU hb'
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe] at this
      apply this
      rw [← hab]
      simpa using ha
    set Wset : Set X := (fun y => y - Y₀) ⁻¹' (V : Set X) with hWdef
    have hWc : IsClopen Wset :=
      ⟨hVc.preimage (continuous_id.sub continuous_const), hVo.preimage (continuous_id.sub continuous_const)⟩
    have hWinv : ∀ s ∈ S, ∀ Y, (Y + s ∈ Wset ↔ Y ∈ Wset) := by
      intro s hs Y
      have hsV : s ∈ V := AddSubgroup.mem_sup_left (hSH hs)
      simp only [Wset, Set.mem_preimage, SetLike.mem_coe]
      rw [show Y + s - Y₀ = (Y - Y₀) + s by abel]
      exact V.add_mem_cancel_right hsV
    obtain ⟨c, hc⟩ := huniq (Wset.indicator f) (hind _ hWc f hf) (by
      intro s hs Y
      by_cases hY : Y ∈ Wset
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem ((hWinv s hs Y).mpr hY), hinv s hs Y]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY ((hWinv s hs Y).mp h))]) (by
      intro Y hY
      by_cases h : Y ∈ Wset
      · rw [Set.indicator_of_mem h, hsupp Y hY]
      · rw [Set.indicator_of_notMem h])
    have e1 := congrFun hc Y₀
    have e2 := congrFun hc x
    have hY₀W : Y₀ ∈ Wset := by simp [Wset, V.zero_mem]
    rw [Set.indicator_of_mem hY₀W] at e1
    rw [Set.indicator_of_notMem (show x ∉ Wset from hxV)] at e2
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    have hc1 : c = 1 := by
      have : (c - 1) * f Y₀ = 0 := by rw [sub_mul, ← e1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hY₀)
    rw [hc1, one_mul] at e2
    exact hx e2.symm
  have hHeq : (H : Set X) = (fun h => Y₀ + h) ⁻¹' {y | f y ≠ 0} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro hh; rw [hH h hh]; exact hY₀
    · intro hne; simpa using hW _ hne
  have hHo : IsOpen (H : Set X) := by
    rw [hHeq]
    exact (isOpen_compl_singleton.preimage hcont).preimage (continuous_const.add continuous_id)
  have hHk : IsCompact (H : Set X) := by
    have hK : IsCompact ((fun h => Y₀ + h) ⁻¹' tsupport f) :=
      (Homeomorph.addLeft Y₀).isCompact_preimage.mpr hf.2
    refine hK.of_isClosed_subset hHcl ?_
    intro h hh
    exact subset_tsupport f (by rw [Function.mem_support, hH h hh]; exact hY₀)
  have hHclo : IsClopen (H : Set X) := ⟨hHcl, hHo⟩
  have h1SB : (H : Set X).indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
    refine ⟨?_, HasCompactSupport.intro' hHk hHcl fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant X ℂ) hHclo).isLocallyConstant
    convert this using 1
    funext x
    first
    | rfl
    | by_cases hx : x ∈ (H : Set X) <;> simp [hx, LocallyConstant.indicator]
  obtain ⟨c, hc⟩ := huniq _ h1SB (by
      intro s hs Y
      have : (Y + s ∈ (H : Set X) ↔ Y ∈ (H : Set X)) := H.add_mem_cancel_right (hSH hs)
      by_cases hY : Y ∈ (H : Set X)
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (this.mpr hY)]; rfl
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (this.mp h))]) (by
      intro Y hY
      refine Set.indicator_of_notMem (fun hYH => hY ?_) _
      have hB0 : Y₀ ∈ B := by
        by_contra h; exact hY₀ (hsupp _ h)
      have hB1 : Y₀ + Y ∈ B := by
        by_contra h; exact hY₀ ((hH Y hYH).symm.trans (hsupp _ h))
      exact hB _ _ hB0 hB1)
  have e0 := congrFun hc 0
  rw [Set.indicator_of_mem (show (0 : X) ∈ (H : Set X) from H.zero_mem)] at e0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at e0
  have hc0 : c ≠ 0 := by
    rintro rfl; simp at e0
  refine ⟨c⁻¹, ?_, hHo, hHk⟩
  funext y
  have ey := congrFun hc y
  simp only [Pi.smul_apply, smul_eq_mul] at ey ⊢
  rw [ey, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.SBClosure

theorem GlobalTheory.SBClosure.main : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {m k : ℕ}
    (S : AddSubgroup (Matrix (Fin m) (Fin k) (Fv F v))) (B : Set (Matrix (Fin m) (Fin k) (Fv F v)))
    (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : Matrix (Fin m) (Fin k) (Fv F v) → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB _) (hf0 : f ≠ 0)
    (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin k) (Fv F v)), (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) →
      ∃ c : ℂ, g = c • f),
    ∃ c : ℂ, f = c • (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))).indicator 1 ∧
      IsOpen (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) ∧ IsCompact (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) := by
  intro F _ _ v m k S B hB f hf hf0 hinv hsupp huniq
  haveI : NonarchimedeanAddGroup (Fin k → Fv F v) := GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin k => Fv F v)
  haveI : NonarchimedeanAddGroup (Matrix (Fin m) (Fin k) (Fv F v)) :=
    GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin m => Fin k → Fv F v)
  exact GlobalTheory.SBClosure.eq_smul_indicator_closure S B hB f hf hf0 hinv hsupp huniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LatVac.DualLoc

variable {F : Type} [Field F] [NumberField F]

theorem form_smul_left {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (u : AF F) (z γ : W) : B (u • z) γ = u * B z γ := by
  rw [co.form, co.form, map_smul]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]

theorem at_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (B z γ) := by
  intro u hu
  rw [smul_eq_mul, ← form_smul_left co, hz u hu, co.form]
  simp

theorem evFin_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z γ : W) :
    evFin F v (B z γ) = (GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2 := by
  rw [co.form]
  simp only [dotProduct, map_sub, map_sum, map_mul]
  rfl

theorem psi_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) :
    ψ (B z γ) = GlobalTheory.LatVac.psiAt ψ v ((GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2) := by
  rw [GlobalTheory.VacIndic.psi_of_at ψ (at_form co v hz γ), ← evFin_form co v z γ]
  rfl

theorem map_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Λ : AddSubgroup W), (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ) →
    (∀ z : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1)) →
    ∀ w : (κ → Fv F v) × (κ → Fv F v), w ∈ Λ.map (GlobalTheory.LatVac.locCo co v) ↔
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), GlobalTheory.LatVac.psiAt ψ v (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
  intro F _ _ v W _ _ B κ _ co ψ Λ hat hdual w
  constructor
  · rintro ⟨z, hz, rfl⟩ l ⟨γ, hγ, rfl⟩
    rw [← psi_form co v ψ (hat z hz) γ]
    exact (hdual z (hat z hz)).1 hz γ hγ
  · intro hw
    obtain ⟨p, hp⟩ : ∃ p : (κ → AF F) × (κ → AF F),
        p = (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) := ⟨_, rfl⟩
    have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (co.e.symm p) := by
      intro u hu
      have hp0 : u • p = 0 := by
        subst hp
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
        · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
      rw [← map_smul, hp0, map_zero]
    have hloc : GlobalTheory.LatVac.locCo co v (co.e.symm p) = w := by
      subst hp
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · show evFin F v ((co.e (co.e.symm _)).1 k) = w.1 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
      · show evFin F v ((co.e (co.e.symm _)).2 k) = w.2 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)
    have hz : co.e.symm p ∈ Λ := (hdual _ hzat).2 fun γ hγ => by
      rw [psi_form co v ψ hzat γ, hloc]
      exact hw _ ⟨γ, hγ, rfl⟩
    exact ⟨_, hz, hloc⟩

end GlobalTheory.LatVac.DualLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNorm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagLevi

theorem det_sub_one_ann {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (e : R)
    (M : Matrix ι ι R) (h : ∀ i j, e * (M i j - (1 : Matrix ι ι R) i j) = 0) : e * (M.det - 1) = 0 := by
  set I : Ideal R := (Submodule.span R {e}).annihilator
  have hI : ∀ a, a ∈ I ↔ a * e = 0 := fun a => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    ext i j
    rw [← map_one (Ideal.Quotient.mk I).mapMatrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, hI, mul_comm]
    exact h i j
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, Matrix.det_one, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hI] at h2
  rw [mul_comm]; exact h2

end GlobalTheory.InertLagLevi

open GlobalTheory.InertLagLevi in
theorem GlobalTheory.InertLagLevi.levi_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl F) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (AE F E), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  intro F E _ _ _ _ _ σ hσ n J hJ v p t hsupp hpt
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := p.1.1 with hP
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := (p⁻¹).1.1 with hQ
  set D : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hD
  set T := t.val with hT
  set Ti := (t⁻¹).val with hTi
  have hTTi : T * Ti = 1 := by simp [T, Ti]
  have hQP : Q * P = 1 := by simp [Q, P]

  have htsupp : ∀ u : AF F, evFin F v u = 0 → u • (T - 1) = 0 := by
    intro u hu
    have h0 : u • (P - 1) = 0 := hsupp u hu
    have h1 : u • (P * D - D) = 0 := by
      rw [show P * D - D = (P - 1) * D by rw [Matrix.sub_mul, Matrix.one_mul], ← Matrix.smul_mul, h0, Matrix.zero_mul]
    rw [show P * D = D * T from hpt, show D * T - D = Matrix.fromRows (T - 1) (T - 1) by
      ext (i|i) j <;> simp [D, diagCols, Matrix.fromRows_mul]] at h1
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) j
    simpa using this
  have hdet : ∀ u : AF F, evFin F v u = 0 → u • (T.det - 1) = 0 := by
    intro u hu
    have h := htsupp u hu
    rw [Algebra.smul_def]
    refine det_sub_one_ann _ T fun i j => ?_
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply, Matrix.sub_apply, Algebra.smul_def] at this
  refine ⟨hdet, ?_, ?_⟩
  · intro u hu
    have hz := hdet u hu
    let b := Module.Free.chooseBasis (AF F) (AE F E)
    rw [Algebra.norm_eq_matrix_det b, smul_eq_mul]
    refine det_sub_one_ann _ _ fun i j => ?_
    rw [← Matrix.sub_apply, ← map_one (Algebra.leftMulMatrix b), ← map_sub, Algebra.leftMulMatrix_eq_repr_mul,
      ← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← smul_mul_assoc, hz, zero_mul, map_zero, Finsupp.zero_apply]
  · have hpt' : P * D = D * T := hpt
    set K : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := Matrix.fromRows 1 (-1) with hKdef
    have hq : Qᵀ * dbl (incM F J) * Q.map (cA σ) = dbl (incM F J) := (p⁻¹).2
    have hQD : Q * D = D * Ti := by
      calc Q * D = Q * (D * T * Ti) := by rw [Matrix.mul_assoc D, hTTi, Matrix.mul_one]
        _ = Q * P * D * Ti := by
          rw [Matrix.mul_assoc Q P D, hpt']; simp only [Matrix.mul_assoc]
        _ = D * Ti := by rw [hQP, Matrix.one_mul]
    have hDc : D.map (cA σ) = D := by
      simp only [D, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    have hK : dbl (incM F J) * D = K * incM F J := by
      simp only [dbl, D, diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
      simp [K, Matrix.fromRows_mul]
    have h2 : Qᵀ * (K * incM F J) * Ti.map (cA σ) = K * incM F J := by
      rw [← hK]
      calc Qᵀ * (dbl (incM F J) * D) * Ti.map (cA σ)
          = Qᵀ * dbl (incM F J) * (D.map (cA σ) * Ti.map (cA σ)) := by rw [hDc]; simp only [Matrix.mul_assoc]
        _ = Qᵀ * dbl (incM F J) * (Q.map (cA σ) * D.map (cA σ)) := by
          have hm1 : (Q * D).map (cA σ) = Q.map (cA σ) * D.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          have hm2 : (D * Ti).map (cA σ) = D.map (cA σ) * Ti.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          rw [← hm1, ← hm2, hQD]
        _ = dbl (incM F J) * D := by rw [hDc, ← Matrix.mul_assoc, hq]
    set X := Q.toBlocks₁₁ - Q.toBlocks₂₁ with hX
    have hQK : Qᵀ * K = Matrix.fromRows Xᵀ (Q.toBlocks₁₂ - Q.toBlocks₂₂)ᵀ := by
      rw [hKdef, ← Matrix.transpose_transpose (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1)),
        ← Matrix.transpose_mul, Matrix.transpose_fromRows]
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks Q]
      rw [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols]
      simp [X, sub_eq_add_neg]
    rw [← Matrix.mul_assoc, hQK, hKdef, Matrix.fromRows_mul, Matrix.fromRows_mul, Matrix.fromRows_mul] at h2
    have h3 : Xᵀ * incM F J * Ti.map (cA σ) = incM F J := by
      have := (Matrix.fromRows_inj h2).1
      rw [this, Matrix.one_mul]
    have hdJ : (incM F J).det = inclR (AF F) J.det := (RingHom.map_det _ J).symm
    have hJu : IsUnit (incM F J).det := hdJ ▸ (Ne.isUnit hJ).map _
    have hdTi : (Ti.map (cA σ)).det = cA σ Ti.det := (AlgHom.map_det (cA σ) Ti).symm
    have hx : X.det * cA σ Ti.det = 1 := by
      have := congrArg Matrix.det h3
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdTi, mul_right_comm] at this
      exact (hJu.mul_left_inj).1 (this.trans (one_mul _).symm)
    have hTd : T.det * Ti.det = 1 := by rw [← Matrix.det_mul, hTTi, Matrix.det_one]
    have hXd : X.det = cA σ T.det := by
      calc X.det = X.det * (cA σ Ti.det * cA σ T.det) := by
            rw [← map_mul, mul_comm Ti.det, hTd, map_one, mul_one]
        _ = (X.det * cA σ Ti.det) * cA σ T.det := by ring
        _ = cA σ T.det := by rw [hx, one_mul]
    refine ⟨Matrix.nonsingInvUnit X (isUnit_iff_exists_inv.mpr ⟨_, hx⟩), rfl, ?_⟩
    show Algebra.norm (AF F) X.det = _
    have hcc : ∀ x, cA σ (cA σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [cA, GlobalTheory.AdelicU.cm_conj_conj hσ]
      | add x y hx hy => simp [hx, hy]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    rw [hXd]
    exact Algebra.norm_eq_of_algEquiv cE T.det
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoDecayOfUnifStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.soDecay_of_prints_of_soDecayUnif : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThKSoDecay.SoDecayUnif → GlobalTheory.ThK.SoDecay := by
  first | exact @GlobalTheory.ThKSoSpan.soDecay_of_unif | exact GlobalTheory.ThKSoSpan.soDecay_of_unif | (intros; apply GlobalTheory.ThKSoSpan.soDecay_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanScaledMappedRowDetsEqPowMulSpanStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)),
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := by
  first | exact @GlobalTheory.span_twistDets_eq | exact GlobalTheory.span_twistDets_eq | (intros; apply GlobalTheory.span_twistDets_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_injectiveRingMap_cancellation : (∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ], Function.Injective φ → ∀ (Y : Scheme.{0}) (a a' : Sp R ⟶ Y), spMap φ ≫ a = spMap φ ≫ a' → a = a') ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), Function.Injective φ → ∀ (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y), a ≫ p = a' ≫ p → spMap φ ≫ a = spMap φ ≫ a' → a = a') := by
  first | exact @GlobalTheory.Nef.spMap_injective_cancel | exact GlobalTheory.Nef.spMap_injective_cancel | (intros; apply GlobalTheory.Nef.spMap_injective_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExistsStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_embedding_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | exact GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | (intros; apply GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsSmallReferenceTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareBottomPairs_small_reference_tuple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  first | exact @GlobalTheory.BotSmall.bottom_small | exact GlobalTheory.BotSmall.bottom_small | (intros; apply GlobalTheory.BotSmall.bottom_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_mu_div_chi_ramified_at_twist_place : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) = v → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  first | exact @GlobalTheory.SqTop.not_unramAt_twist | exact GlobalTheory.SqTop.not_unramAt_twist | (intros; apply GlobalTheory.SqTop.not_unramAt_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleIsCMValueHeckeCharacterStatement
section
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_nu_twisted_tuple_isCMValueHeckeCharacter : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m) {s : ℕ}, s ≤ GlobalTheory.FunObj.SqNum.halfRank D i j → GlobalTheory.CMVal.IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D sc.cGap i j s) (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (GlobalTheory.FunObj.SqNum.nuH G t i j) := by
  first | exact @GlobalTheory.SqTop.TwVal.isValChar_nu_twist | exact GlobalTheory.SqTop.TwVal.isValChar_nu_twist | (intros; apply GlobalTheory.SqTop.TwVal.isValChar_nu_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharFiniteRationalEqExp
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.StdFinRat

theorem std_fin_rat : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : F,
    ψ (pairA F 0 (algebraMap F (Af F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) :=
  fun _ _ _ _ hψ x => GlobalTheory.PsiNontriv.isStd_fin_rat hψ x

end GlobalTheory.StdFinRat
end

