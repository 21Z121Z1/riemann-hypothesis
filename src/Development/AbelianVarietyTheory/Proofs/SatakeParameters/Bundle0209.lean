import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineWeilDeligneSpaceRestrictionEquiv
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Pst.ResLetter

open TensorProduct Module

theorem zpow_intertwine {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (T : M →+ N) (a : (Module.End R M)ˣ) (b : (Module.End R N)ˣ) (hab : ∀ x, T ((a : Module.End R M) x) = (b : Module.End R N) (T x)) (n : ℤ) (x : M) :
    T (((a ^ n : (Module.End R M)ˣ) : Module.End R M) x) = ((b ^ n : (Module.End R N)ˣ) : Module.End R N) (T x) := by
  have hinv : ∀ y, T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y) =
      ((b⁻¹ : (Module.End R N)ˣ) : Module.End R N) (T y) := by
    intro y
    have h1 : (b : Module.End R N) (T (((a⁻¹ : (Module.End R M)ˣ) : Module.End R M) y)) = T y := by
      rw [← hab, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]
    rw [← h1, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hab]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ih, hinv]

section Gen

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : FinExt l} {V : Type} [AddCommGroup V]
  [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] {K K' : FinExt l}
  (ρ : Representation ↥LL.1 ↥(GK K) V) (hle : K.1 ≤ K'.1)

def toRes : ↥(Dpst P ρ) →+ ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) where
  toFun x := ⟨x.1, by rw [GlobalTheory.Pst.Dpst_resTo]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def ofRes : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)) →+ ↥(Dpst P ρ) where
  toFun x := ⟨x.1, by rw [← GlobalTheory.Pst.Dpst_resTo P ρ hle]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toRes_ofRes (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) : toRes P ρ hle (ofRes P ρ hle x) = x := rfl
theorem ofRes_toRes (x : ↥(Dpst P ρ)) : ofRes P ρ hle (toRes P ρ hle x) = x := rfl

theorem toRes_smul (a : ↥LL.1) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (a • x) = (RingHom.id _ a) • toRes P ρ hle x := rfl
theorem ofRes_smul (a : ↥LL.1) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle (a • x) = (RingHom.id _ a) • ofRes P ρ hle x := rfl

theorem toRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (mulD P ρ c x) = mulD P (GlobalTheory.Pst.resTo ρ hle) c (toRes P ρ hle x) := rfl
theorem ofRes_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) :
    ofRes P ρ hle (mulD P (GlobalTheory.Pst.resTo ρ hle) c x) = mulD P ρ c (ofRes P ρ hle x) := rfl
theorem toRes_phiD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (phiD P ρ x) = phiD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl
theorem toRes_monD (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (monD P ρ x) = monD P (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) := rfl

theorem toRes_actD (g : ↥(GK K)) (g' : ↥(GK K')) (hg : (g' : GQ l) = (g : GQ l)) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (actD P ρ g x) = actD P (GlobalTheory.Pst.resTo ρ hle) g' (toRes P ρ hle x) := by
  have e : Subgroup.inclusion (GK_le hle) g' = g := Subtype.ext hg
  subst e
  rfl

theorem toRes_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))] (n : ℤ) (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (((phiU P ρ ^ n : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x) =
      ((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ n : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
        End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x) :=
  zpow_intertwine (toRes P ρ hle) (phiU P ρ) (phiU P (GlobalTheory.Pst.resTo ρ hle)) (fun y => toRes_phiD P ρ hle y) n x

end Gen

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L Ω : Type} [Field Ω] [Field K] [NumberField K]
  [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O']
  [TopologicalSpace O'] {Bw : LocBridge l K Ω (Dec (F := K) A) O} {Bw' : LocBridge l L Ω (Dec (F := L) A) O'}
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]

theorem alpha_eq (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) : alpha l σ' = alpha l σ := by
  have e := GlobalTheory.LocLanglands.normV_zpow_deg_eq σ' σ hσ
  rw [GlobalTheory.Pst.normV_eq_pow (hj'.mem_placesOver h'), GlobalTheory.Pst.normV_eq_pow (hj.mem_placesOver h)] at e
  push_cast at e
  simp only [← zpow_natCast, ← zpow_mul] at e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact zpow_right_injective₀ (zero_lt_one.trans hl) hl.ne' e

variable (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hle : Bw.Kw.1 ≤ Bw'.Kw.1)
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))]

theorem toRes_weilD (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (x : ↥(Dpst P ρ)) :
    toRes P ρ hle (weilD Bw h P ρ σ x) = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by
  calc toRes P ρ hle (weilD Bw h P ρ σ x)
      = toRes P ρ hle (actD P ρ (weilToGK Bw h σ)
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) := rfl
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ') (toRes P ρ hle
          (((phiU P ρ ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) x)) :=
        toRes_actD P ρ hle _ _ hg _
    _ = actD P (GlobalTheory.Pst.resTo ρ hle) (weilToGK Bw' h' σ')
          (((phiU P (GlobalTheory.Pst.resTo ρ hle) ^ (-alpha l σ) : (End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle)))ˣ) :
            End ↥LL.1 ↥(Dpst P (GlobalTheory.Pst.resTo ρ hle))) (toRes P ρ hle x)) :=
        congrArg _ (toRes_phiU_zpow P ρ hle _ x)
    _ = weilD Bw' h' P (GlobalTheory.Pst.resTo ρ hle) σ' (toRes P ρ hle x) := by rw [← ha]; rfl

variable (ι : Om l ≃+* ℂ)

theorem wdHom_ext {M : Type*} [AddCommGroup M] [Module ℂ M] {f g : WDSpace P ι ρ →ₗ[ℂ] M}
    (hfg : ∀ x, f (wdMk P ι ρ x) = g (wdMk P ι ρ x)) : f = g :=
  LinearMap.ext_on_range (span_wdMk P ι ρ) hfg

def resEquiv : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle) :=
  letI := algC ι LL
  LinearEquiv.ofLinear
    (EnlargeCoeff.chg (mulD P ρ) (mulD P (GlobalTheory.Pst.resTo ρ hle)) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (toRes P ρ hle) (toRes_smul P ρ hle) (toRes_mulD P ρ hle))
    (EnlargeCoeff.chg (mulD P (GlobalTheory.Pst.resTo ρ hle)) (mulD P ρ) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      (ofRes P ρ hle) (ofRes_smul P ρ hle) (ofRes_mulD P ρ hle))
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, toRes_ofRes, LinearMap.id_apply])
    (letter_hom_ext _ _ _ fun x => by
      rw [LinearMap.comp_apply, EnlargeCoeff.chg_mk, EnlargeCoeff.chg_mk, ofRes_toRes, LinearMap.id_apply])

theorem resEquiv_mk (x : ↥(Dpst P ρ)) :
    resEquiv P ρ hle ι (wdMk P ι ρ x) = wdMk P ι (GlobalTheory.Pst.resTo ρ hle) (toRes P ρ hle x) :=
  letI := algC ι LL
  EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ (toRes_mulD P ρ hle) x

theorem resEquiv_wdN (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdN P ι ρ y) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdN P ι ρ =
      wdN P ι (GlobalTheory.Pst.resTo ρ hle) ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdN_mk, resEquiv_mk, toRes_monD]
  exact LinearMap.congr_fun this y

theorem resEquiv_wdRho (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (σ : Weil h) (σ' : Weil h')
    (hg : (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) (ha : alpha l σ' = alpha l σ)
    (y : WDSpace P ι ρ) :
    resEquiv P ρ hle ι (wdRho P ι Bw h hj ρ σ y) =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (resEquiv P ρ hle ι y) := by
  have : (resEquiv P ρ hle ι).toLinearMap ∘ₗ wdRho P ι Bw h hj ρ σ =
      wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' ∘ₗ (resEquiv P ρ hle ι).toLinearMap :=
    wdHom_ext P ρ ι fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wdRho_mk, resEquiv_mk, toRes_weilD P ρ hle σ σ' hg ha]
  exact LinearMap.congr_fun this y

end Weil

theorem wdSpace_resTo_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  intro l _ P ι K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' O O' _ _ _ _ _ _ Bw Bw' hj hj' hle hW LL V _ _ _ _ _ ρ _ _ _
  exact ⟨resEquiv P ρ hle ι, fun σ σ' hσ x =>
    resEquiv_wdRho P ρ hle ι hj hj' σ σ' (hW σ σ' hσ) (alpha_eq hj hj' σ σ' hσ) x,
    fun x => resEquiv_wdN P ρ hle ι x⟩

end GlobalTheory.Pst.ResLetter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GalRepRankTwo
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp

set_option maxHeartbeats 2000000 in

theorem galRep_rankTwo : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.LocalGlobalAboveL → GlobalTheory.Published.RegularAlgebraicPurity → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (i : D.nd.Loc) (a : ℕ), 2 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2) ∧ D.naut.tempered (D.naut.locG π w)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2) := by
  intro hF hG hLG hRP hL D P i a ha π hc hr
  have := host_isCMField D.host
  have ha1 : 1 ≤ a := by omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (P.cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd D.nd.Om (D.naut.iotaQC i) ha1 hr₀ hc₀
  have hcoh := (hRP D.host.E a ha1 π₀ hr₀).2
  have hcont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) := Units.continuous_val.comp H.cont
  have hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, hmk]
    rfl
  have haway : ∀ (w : PlE D.host) (hl : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      wdOf (D.nd.plOm.2 w) hl (D.naut.iotaQC i) r =
        P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := fun w hl => by
    rw [wdOfEqLocPar hL hF H hl, hloc]
  have hv : (1 - (a : ℝ)) / 2 + (wt : ℝ) / 2 = 0 := by
    refine exponentEqZero D.naut ha1 π hc (D.nd.l i) _ fun w hl => ?_
    have h1 := H.tempered_wdOf hl (D.nd.plOm.2 w)
    rw [haway w hl, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add] at h1
    exact h1
  have htemp : ∀ w : PlE D.host, ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal →
      D.naut.tempered (D.naut.locG π w) := fun w hl => by
    have h1 := H.tempered_wdOf hl (D.nd.plOm.2 w)
    rw [haway w hl, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add, hv, D.naut.lpTw_zero] at h1
    exact h1
  have hWaway : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i r w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2) := fun w hw => by
    rw [(P.wdOf i a r w).1]
    exact (P.T.e w).injective (by rw [P.wd.away _ _ r w hw, haway w hw])
  obtain ⟨K, ρ, hρc, hρ⟩ := finextRep (D.nd.l i) D.host.E D.nd.Om a r hcont
  have hside : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w ∧
      ∀ τ : D.host.E →+* Qbar (D.nd.l i), (∀ (A : ValuationSubring D.nd.Om), IsPlaceOver A w →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
          (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) A) O),
          Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Bw.LL.1, IsInduced Bw τ τ') →
        P.wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ = HT τ := by
    intro w hw
    obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge (D.nd.l i) D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w)
    obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
    have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
    let LL' : FinExt (D.nd.l i) := supExt K Bw.LL
    have hK : K.1 ≤ LL'.1 := le_sup_left
    have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
    let ρ' : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
    have hρ' : mapRep (algebraMap ↥LL'.1 (Om (D.nd.l i))) ρ' = r := by
      rw [← hρ]
      ext g i k
      rfl
    have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin a) (Fin a) ↥LL'.1) := by
      have hi : Continuous (IntermediateField.inclusion hK) :=
        continuous_induced_rng.2 continuous_subtype_val
      exact hρc.matrix_map hi
    have hmodel : IsModel Bw (resDec D.nd.plOm.1 r w) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      ⟨hB, by rw [← hρ']; rfl⟩
    let φ : ↥(OL L0) →+* Qbar (D.nd.l i) := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
    have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om (D.nd.l i)) := fun x => (hBto x).symm
    have hcl := (P.wd.loc (D.nd.l i) (D.naut.iotaQC i) w hw _ Bw hind φ hφ).2 LL' hB a ρ' hρ'c
    rw [hρ'] at hcl
    have hab := H.above (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hind
    have hdR : Bw.IsdRE (D.loc (D.nd.l i)) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      (hmodel.isdRAt_iff (D.loc (D.nd.l i))).1 hab.deRham
    refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
    obtain ⟨τ₀, hτ₀⟩ := hτ _ (D.nd.plOm.2 w) _ Bw hind
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
    have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
    have hJ := hab.jumps τ LL' τ'' hτ''
    ext n
    apply Nat.cast_injective (R := ℤ)
    rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc (D.nd.l i)) hmodel hτ'' hJ n]
  refine ⟨r, hcont, H.ss, fun w hw => ⟨hWaway w hw, htemp w hw⟩, fun w hw => ⟨?_, fun τ _ => ?_, ?_⟩⟩
  · exact ((P.wdOf i a r w).2.2.2.1).2 (hside w hw).1
  · obtain ⟨w', hw', hτ⟩ := existsIsInduced (D.nd.l i) D.host.E D.nd.Om τ
    rw [(P.wdOf i a r w).2.2.2.2 τ, (hside w' hw').2 τ hτ]
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights, D.naut.jumpsInf_def i π τ hr, hinf]
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  · rw [(P.wdOf i a r w).1]
    obtain ⟨LL, Bw', hj', he⟩ := P.wd.above _ (D.naut.iotaQC i) r w hw
    obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ π₀ w
    have h2 := hLG D.host.E D.nd.Om (D.nd.l i) (D.naut.iotaQC i) a ha π₀ hc₀ hcoh r wt HT H (D.loc _) (D.locA _)
      ⟨D.locT _⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw' hj' σ₀ hσ₀ _ (ParLaws.isRec_locRec hL (D.nd.plOm.2 w))
    refine (P.T.e w).injective ?_
    rw [he]
    refine h2.trans ?_
    rw [rec_algNorm (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) σ₀, hloc, ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
    rfl

end GlobalTheory.GalFirstClause
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsTwistByDeRhamCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.TwistJumpsW
open Formalism.BasicNotions.Loc

theorem jumpsW_twist : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  intro D T W i ι a ρ χ hρ hχ τ c hdR hc
  let w := PI.CompDegEF.plOf τ
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := PI.CompDegEF.natCast_mem_plIdeal τ
  have hIW : InducesW D.nd i τ w := fun x => Iff.rfl
  obtain ⟨hdρ, hdχ⟩ := hdR w hIW
  have hj : GlobalTheory.Pst.Induces (D.nbr i w hw) := D.nbr_ind i w hw
  obtain ⟨L₁, hL₁, hm₁⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) a ρ hρ
    (D.nbr i w hw).LL
  obtain ⟨L, hL, hm⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) 1 χ hχ L₁
  have hBL : (D.nbr i w hw).LL.1 ≤ L.1 := hL₁.trans hL
  obtain ⟨τ', hτ'⟩ := GlobalTheory.EmbExt.main D (D.nd.l i) w _ (D.nbr i w hw) hj τ hIW L hBL
  obtain ⟨ρ₁, cρ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem ρ hρ L (fun g i j => hL (hm₁ g i j))
  obtain ⟨χ₁, cχ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem χ hχ L hm
  obtain ⟨-, H⟩ := W.loc (D.nd.l i) ι w hw _ (D.nbr i w hw) hj
    ((algebraMap ↥(D.nbr i w hw).LL.1 (Om (D.nd.l i))).comp (D.nbr i w hw).toLL) (fun _ => rfl)
  let tw₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L.1 := GlobalTheory.TwistAbove.twGL (Matrix.GeneralLinearGroup.det.comp χ₁) ρ₁
  have htw : Formalism.MainNotions.SumRepresentations.At.twGL (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁)
      (Matrix.GeneralLinearGroup.det.comp (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) χ₁)) =
      mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) tw₁ := by
    refine MonoidHom.ext fun g => Units.ext ?_
    ext p q
    simp [tw₁, mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  have ctw : Continuous (fun g => ((tw₁ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1)) := by
    have h1 : Continuous (fun g => ((χ₁ g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1).det) := cχ.matrix_det
    refine continuous_matrix fun p q => ?_
    refine (h1.mul (cρ.matrix_elem p q)).congr fun g => ?_
    simp [tw₁, GlobalTheory.TwistAbove.twGL_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [htw]
  have Hρ := H L hBL a ρ₁ cρ
  have Hχ := H L hBL 1 χ₁ cχ
  have Htw := H L hBL a tw₁ ctw
  have dρ := Hρ.2.1.1 hdρ
  have dχ := Hχ.2.1.1 hdχ
  have hcom := GlobalTheory.TwistAbove.twist_common (D.nbr i w hw) (ρ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)
    (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) (D.locT (D.nd.l i))
  have dtw : (D.nbr i w hw).IsdRE (D.loc (D.nd.l i)) L (tw₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    hcom.1 dρ dχ
  have mχ : ∀ n, (D.nbr i w hw).multE (D.loc (D.nd.l i)) L (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' n =
      if n = c then 1 else 0 := by
    intro n
    rw [← (Hχ.2.2.2 τ τ' hτ').2 dχ n, hc, Multiset.count_singleton]
    split_ifs <;> simp
  ext n
  have e1 := (Htw.2.2.2 τ τ' hτ').2 dtw n
  have e2 := hcom.2.2.2 τ' c dχ mχ (n - c)
  have e3 := (Hρ.2.2.2 τ τ' hτ').2 dρ (n - c)
  have e4 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) (W.jumpsW (D.nd.l i) ι (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁) τ)
    (add_left_injective c) (n - c)
  simp only [sub_add_cancel] at e2 e4
  rw [e4]
  exact_mod_cast e1.trans (e2.trans e3.symm)

end GlobalTheory.TwistJumpsW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesDualStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicCoordinates_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → TrDual (nP D p) σ om oms → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → ∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf' D p σ oms R g e' i = if e = e' then 1 else 0 := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual | exact GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIntegralSigmaSqFixedStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicCoordinates_integral_sigma_sq_fixed : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → (∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) → OwOK (nP D p) σ om oms → (∀ z a b i, ‖g z a b i‖ ≤ 1) → (∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) → (∀ e i, ‖fOf D p σ om R g e i‖ ≤ 1 ∧ σ (σ (fOf D p σ om R g e i)) = fOf D p σ om R g e i) ∧ (∀ e i, ‖fOf' D p σ oms R g e i‖ ≤ 1 ∧ σ (σ (fOf' D p σ oms R g e i)) = fOf' D p σ oms R g e i) := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq | exact GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIsotropicStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicCoordinates_isotropic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → (∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf D p σ om R g e' i = 0) ∧ (∀ e e', ∑ i, σ (fOf' D p σ oms R g e i) * fOf' D p σ oms R g e' i = 0) := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_isotropic | exact GlobalTheory.KerStd.HypCoord.fOf_isotropic | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InducedProductCommutesFamilyProduct
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ProdReorder
section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_single_equiv {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) :
    Nonempty ((multiProd e fun a => (τ a).π).Equiv (τ 0).π) := by
  have A := multiProd_head (k := k) (fun a => (τ a).π) e (by simp : dτ 0 + 0 = dτ 0)
          (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  have B := ind₂_unit_right (k := k) (by simp : dτ 0 + 0 = dτ 0) (τ 0).π (τ 0).smooth (fun a : Fin 0 => (τ a.succ).π) (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem commutes_multiProd_single {p : ℕ} (x : Irr k p) {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (hc : Commutes x (τ 0)) (N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) (h₁ : p + dτ 0 = N) (h₂ : dτ 0 + p = N) : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have M := multiProd_single_equiv τ e
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₁) (extTensor x.π (τ 0).π))) := ind₂_congr h₁ (eqv_refl _) M
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (τ 0).π)).Equiv (ind₂ (stdSum h₂) (extTensor (τ 0).π x.π))) := hc N h₁ h₂
  have s3 : Nonempty ((ind₂ (stdSum h₂) (extTensor (τ 0).π x.π)).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := ind₂_congr h₂ (eqv_symm M) (eqv_refl _)
  exact s1.elim fun a => s2.elim fun b => s3.elim fun c => ⟨(a.trans b).trans c⟩

theorem commutes_ind₂_of_head {p d T' T N : ℕ} (x : Irr k p) (y : Irr k d) {W : Type} [AddCommGroup W] [Module ℂ W]
    (R : Representation ℂ (GL (Fin T') k) W) (sR : IsSmooth R) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (P : Representation ℂ (GL (Fin T) k) Y) (h : d + T' = T) (H : Nonempty (P.Equiv (ind₂ (stdSum h) (extTensor y.π R))))
    (hc : Commutes x y)
    (IH : ∀ M (g₁ : p + T' = M) (g₂ : T' + p = M),
      Nonempty ((ind₂ (stdSum g₁) (extTensor x.π R)).Equiv (ind₂ (stdSum g₂) (extTensor R x.π))))
    (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv (ind₂ (stdSum h₂) (extTensor P x.π))) := by
  have hA2 : (p + d) + T' = N := by omega
  have hB1 : d + p = p + d := Nat.add_comm _ _
  have h₄ : d + (p + T') = N := by omega
  have hD : T' + p = p + T' := Nat.add_comm _ _
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv
      (ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R))))) :=
    ind₂_congr h₁ (eqv_refl x.π) H
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R)))).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R))) :=
    (ind₂_assoc' (k := k) rfl hA2 h h₁ x.π y.π R x.smooth y.smooth sR).elim fun a => ⟨a.symm⟩
  have s3 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R)).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R))) :=
    ind₂_congr hA2 (hc (p + d) rfl hB1) (eqv_refl R)
  have s4 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R)).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R))))) :=
    ind₂_assoc' (k := k) hB1 hA2 rfl h₄ y.π x.π R y.smooth x.smooth sR
  have s5 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R)))).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π))))) :=
    ind₂_congr h₄ (eqv_refl y.π) (IH _ rfl hD)
  have s6 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π)))).Equiv
      (ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π))) :=
    (ind₂_assoc' (k := k) h h₂ hD h₄ y.π R x.π y.smooth sR x.smooth).elim fun a => ⟨a.symm⟩
  have s7 : Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π)).Equiv
      (ind₂ (stdSum h₂) (extTensor P x.π))) :=
    ind₂_congr h₂ (H.elim fun a => ⟨a.symm⟩) (eqv_refl x.π)
  exact s1.elim fun a1 => s2.elim fun a2 => s3.elim fun a3 => s4.elim fun a4 => s5.elim fun a5 =>
    s6.elim fun a6 => s7.elim fun a7 => ⟨a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))⟩

end SlopeTestRemainingChoices

section Succ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem commutes_multiProd_succ {p s : ℕ} (x : Irr k p)
    (ih : ∀ (dτ : Fin s → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))))
    (dτ : Fin (s + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)) (hc : ∀ a, Commutes x (τ a)) (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have key : ∀ (S : ℕ) (e' : (Σ a : Fin s, Fin (dτ a.succ)) ≃ Fin S) (h : dτ 0 + S = T),
      Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
    intro S e' h
    have H := multiProd_head (k := k) (fun a => (τ a).π) e h e'
    have sR : IsSmooth (multiProd e' fun a : Fin s => (τ a.succ).π) :=
      GlobalTheory.SmGL.isSmooth_parInd e' (piTensor fun a : Fin s => (τ a.succ).π)
    exact commutes_ind₂_of_head x (τ 0) _ sR _ h H (hc 0)
      (fun M g₁ g₂ => ih (fun a => dτ a.succ) (fun a => τ a.succ) (fun a => hc a.succ) _ M e' g₁ g₂) h₁ h₂
  have h : dτ 0 + ∑ a : Fin s, dτ a.succ = T := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    rw [← this]
    exact (Fin.sum_univ_succ _).symm
  exact key _ (finSigmaFinEquiv (n := fun a : Fin s => dτ a.succ)) h
end Succ

theorem commutes_multiProd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p u : ℕ) (x : Irr k p) (dτ : Fin (u + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  intro k _ _ _ _ p u x
  induction u with
  | zero =>
    intro dτ τ hc T N e h₁ h₂
    have hT : T = dτ 0 := by
      have := Fintype.card_congr e
      simpa [Fintype.card_sigma] using this.symm
    subst hT
    exact commutes_multiProd_single x τ (hc 0) N e h₁ h₂
  | succ u ih =>
    exact commutes_multiProd_succ x ih

end GlobalTheory.ProdReorder
end

