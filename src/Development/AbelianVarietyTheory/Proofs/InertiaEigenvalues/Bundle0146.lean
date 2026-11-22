import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.KernelDictionary
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0083
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0133
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import GroundTheory.LocalFields.UnramifiedNormSurj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.TrivCrys

open Module TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
private theorem lid_rTensor_map_id_eq {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] (f : V →ₗ[Qp] Qp) (σ : B →ₗ[Qp] B) (x : V ⊗[Qp] B) :
    TensorProduct.lid Qp B (LinearMap.rTensor B f
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) σ x)) =
      σ (TensorProduct.lid Qp B (LinearMap.rTensor B f x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
private theorem eq_sum_basis_tmul_coord {V : Type} [AddCommGroup V] [Module Qp V] {ι : Type}
    [Fintype ι] (b : Basis ι Qp V) (x : V ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
    simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]

open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in

theorem _root_.GlobalTheory.TrivCrys.dcris_of_trivial {V : Type} [AddCommGroup V] [Module Qp V]
    [Module LL V] [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  have hid : ∀ g, ρ g = LinearMap.id := fun g => LinearMap.ext (hρ g)
  ext x
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris, LinearMap.mem_range]
  constructor
  · intro hx
    let b := Module.finBasis Qp V
    have hc : ∀ i, ∃ k : K₀, algebraMap K₀ B k =
        TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
      intro i
      refine (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.invariantsEq PD _).mp fun g => ?_
      have h := hx g
      unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB at h
      rw [hid g] at h
      conv_rhs => rw [← h]
      rw [lid_rTensor_map_id_eq]
      rfl
    choose k hk using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] k i, ?_⟩
    rw [map_sum, eq_sum_basis_tmul_coord b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraTensorModule.map_tmul, ← hk i]
    rfl
  · rintro ⟨y, rfl⟩ g
    unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB
    rw [hid g]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add y z hy hz => simp only [map_add, hy, hz]

open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in

theorem _root_.GlobalTheory.TrivCrys.isCrys_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) : _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys PD ρ := by
  haveI := _root_.GlobalTheory.Survey.CrystallineCyclotomic.nontrivial_B PD
  have key : ⇑(AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) =
      ⇑(LinearMap.lTensor V (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add u w hu hw => simp only [map_add, hu, hw]
  have hinj : Function.Injective (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    rw [key]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (fun a c h => (algebraMap K₀ B).injective h)
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys
  rw [_root_.GlobalTheory.TrivCrys.dcris_of_trivial PD ρ hρ, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_tensorProduct, mul_comm]

open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in

theorem _root_.GlobalTheory.TrivCrys.isCrys_lat_of_trivial : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [FiniteDimensional Qp LL] (U : _root_.Formalism.BasicNotions.LocLat G Qp LL O), (∀ g x, U.ρ g x = x) → _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys PD U.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ _ U hU
  haveI := U.fdim
  haveI : FiniteDimensional Qp U.V := Module.Finite.trans LL U.V
  exact _root_.GlobalTheory.TrivCrys.isCrys_of_trivial PD U.ρ hU

end GlobalTheory.TrivCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportJacquetRallisDesc
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem norm_eq_of_sub_lt {F : Type} [NormedField F] [IsUltrametricDist F] {x y : F}
    (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have h1 : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (x - y) y
  have h2 : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (y - x) x
  rw [norm_sub_rev] at h2
  rcases le_total ‖x - y‖ ‖y‖ with h3 | h3
  · rw [max_eq_right h3] at h1
    rcases le_total ‖x - y‖ ‖x‖ with h4 | h4
    · rw [max_eq_right h4] at h2; exact le_antisymm h1 h2
    · rw [max_eq_left h4] at h2; exact absurd h (not_lt.mpr h2)
  · exact absurd h (not_lt.mpr h3)

theorem eta_det_isLocallyConstant {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    IsLocallyConstant (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hd : ((g : Matrix (Fin r) (Fin r) F).det) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hc : Continuous (fun h : GL (Fin r) F => (h : Matrix (Fin r) (Fin r) F).det) :=
    Units.continuous_val.matrix_det
  have hpos : 0 < ‖(g : Matrix (Fin r) (Fin r) F).det‖ := norm_pos_iff.mpr hd
  have hev : ∀ᶠ h : GL (Fin r) F in 𝓝 g, ‖((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖ <
      ‖(g : Matrix (Fin r) (Fin r) F).det‖ := by
    have : Continuous (fun h : GL (Fin r) F =>
        ‖(h : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖) :=
      (hc.sub continuous_const).norm
    exact (this.tendsto g).eventually_lt_const (by rw [sub_self, norm_zero]; exact hpos)
  filter_upwards [hev] with h hh
  unfold eta
  rw [norm_eq_of_sub_lt hh]

set_option maxHeartbeats 800000 in

theorem desc_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → IsTest (LinDesc.desc A M hG lam α f') := by
  intro F E _ _ _ _ hU A r τ p hG lam M α f' hf hα hαc
  haveI : IsUltrametricDist F := hU.ultraF

  let ρL : A.K →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i => (Algebra.trace F A.K).comp (LinearMap.mulLeft F (τ ^ (i : ℕ)))
  have hρL : ∀ c, ρL c = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c) := fun c => rfl
  have hbij : Function.Bijective ρL := by
    have := (GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hG).1
    rw [show (⇑ρL) = fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a) from funext hρL]
    exact this
  let ρE : A.K ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective ρL hbij
  have hι : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.toLinearMap
  have hρ : Continuous ρL := IsModuleTopology.continuous_of_linearMap (R := F) ρL
  have hιs : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.symm.toLinearMap
  have hρs : Continuous ρE.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) ρE.symm.toLinearMap
  have hpt : Continuous (fun x : A.K × A.K => pt A hG lam x.1 x.2) := by
    unfold pt
    exact continuous_const.prodMk ((hι.comp continuous_fst).prodMk
      ((hρ.comp continuous_snd).prodMk continuous_const))
  have hact : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1 q.2) := by
    unfold act
    have h1 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1 : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp continuous_fst
    have h2 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
      ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
        (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
          (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))
  have heta := eta_det_isLocallyConstant (F := F) r

  have hΦ : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F =>
      f' (act q.2 (pt A hG lam q.1.1 q.1.2)) * eta ((q.2 : Matrix (Fin r) (Fin r) F).det) * (α q.2 : ℂ)) := by
    have a1 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => f' (act q.2 (pt A hG lam q.1.1 q.1.2))) :=
      hf.1.comp_continuous (hact.comp (continuous_snd.prodMk (hpt.comp continuous_fst)))
    have a2 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => eta ((q.2 : Matrix (Fin r) (Fin r) F).det)) :=
      heta.comp_continuous continuous_snd
    have a3 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => (α q.2 : ℂ)) :=
      (hα.comp_continuous continuous_snd).comp (fun t : ℝ => (t : ℂ))
    exact (a1.mul a2).mul a3
  have hloc : IsLocallyConstant (LinDesc.desc A M hG lam α f') := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have h1 : ∀ᶠ x in 𝓝 x₀, ∀ g ∈ tsupport α,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) =
          f' (act g (pt A hG lam x₀.1 x₀.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) := by
      refine hαc.eventually_forall_of_forall_eventually fun g _ => ?_
      have h2 := (hΦ.prodMk (hΦ.comp_continuous (f := fun q : (A.K × A.K) × GL (Fin r) F => (x₀, q.2))
        (continuous_const.prodMk continuous_snd))).eventually_eq (x₀, g)
      filter_upwards [h2] with q hq
      simp only [Prod.mk.injEq, Function.comp] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with x hx
    unfold desc
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hx g hg
    · rw [image_eq_zero_of_notMem_tsupport hg]; simp
  refine ⟨hloc, ?_⟩

  let L : (Fin r → F) × (Fin r → F) → A.K × A.K := fun u => ((bas A hG).equivFun.symm u.1, ρE.symm u.2)
  have hL : Continuous L := (hιs.comp continuous_fst).prodMk (hρs.comp continuous_snd)
  let T : GL (Fin r) F × Gl r F → A.K × A.K := fun q => L ((act q.1⁻¹ q.2).2.1, (act q.1⁻¹ q.2).2.2.1)
  have hT : Continuous T := by
    have : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1⁻¹ q.2) :=
      hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
    exact hL.comp ((continuous_fst.comp (continuous_snd.comp this)).prodMk
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp this))))
  have hS : IsCompact (T '' (tsupport α ×ˢ tsupport f')) := (hαc.prod hf.2).image hT
  have hsub : Function.support (LinDesc.desc A M hG lam α f') ⊆ T '' (tsupport α ×ˢ tsupport f') := by
    intro x hx
    by_contra hxS
    apply hx
    have h0 : ∀ g : GL (Fin r) F,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) = 0 := by
      intro g
      by_contra hne
      apply hxS
      have hαg : α g ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      have hfg : f' (act g (pt A hG lam x.1 x.2)) ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      refine ⟨(g, act g (pt A hG lam x.1 x.2)), ⟨subset_tsupport _ hαg, subset_tsupport _ hfg⟩, ?_⟩
      have hback : act g⁻¹ (act g (pt A hG lam x.1 x.2)) = pt A hG lam x.1 x.2 := by
        rw [← act_mul, inv_mul_cancel, act_one]
      show L ((act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.1, (act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.2.1) = x
      rw [hback]
      show ((bas A hG).equivFun.symm ((bas A hG).equivFun x.1), ρE.symm (ρL x.2)) = x
      rw [LinearEquiv.symm_apply_apply]
      have : ρE.symm (ρL x.2) = x.2 := ρE.symm_apply_apply x.2
      rw [this]
    unfold desc
    simp only [h0, integral_zero]
  have hcl : IsClosed (Function.support (LinDesc.desc A M hG lam α f')) := by
    have := hloc.isOpen_fiber 0
    rw [← isOpen_compl_iff]
    convert this using 1
    ext x; simp
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hS.of_isClosed_subset hcl hsub

end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCo
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbTest

theorem eta_eq_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  unfold eta
  by_cases hx : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [if_pos hx, if_pos (h ▸ hx)]
  · rw [if_neg hx, if_neg (h ▸ hx)]

theorem isLocallyConstant_eta_comp {X F : Type} [TopologicalSpace X] [NormedField F] [IsUltrametricDist F]
    (h : X → F) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) : IsLocallyConstant (fun x => eta (h x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : 0 < ‖h x‖ := norm_pos_iff.mpr (h0 x)
  have hev : ∀ᶠ y in 𝓝 x, dist (h y) (h x) < ‖h x‖ := (hc.tendsto x) (Metric.ball_mem_nhds _ hx)
  filter_upwards [hev] with y hy
  apply eta_eq_of_norm_eq
  rw [dist_eq_norm] at hy
  have hy' : ‖h x - h y‖ < ‖h x‖ := by rwa [norm_sub_rev]
  have e1 : ‖h y‖ ≤ max ‖h y - h x‖ ‖h x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h y - h x) (h x)
  have e2 : ‖h x‖ ≤ max ‖h x - h y‖ ‖h y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h x - h y) (h y)
  apply le_antisymm
  · exact e1.trans (max_le hy.le le_rfl)
  · rcases le_total ‖h x - h y‖ ‖h y‖ with hh | hh
    · exact e2.trans (max_le hh le_rfl)
    · exact absurd (e2.trans (max_le le_rfl hh)) (not_le.mpr hy')

theorem continuous_act {r : ℕ} {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] (Y : Gl r k) :
    Continuous (fun g : GL (Fin r) k => act g Y) := by
  unfold act
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const))
  · exact (Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv
  · exact Units.continuous_val.matrix_mulVec continuous_const
  · exact continuous_const.matrix_vecMul Units.continuous_coe_inv

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem continuous_actU {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousStar E] (X : Hn r F E) :
    Continuous (fun g : Matrix.unitaryGroup (Fin r) E => actU g X) := by
  unfold actU
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
  · exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul continuous_subtype_val.star
  · exact continuous_subtype_val.matrix_mulVec continuous_const

end GlobalTheory.JR.OrbTest

namespace GlobalTheory.JR.OrbTest

theorem isTest_orbG_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f' : Gl r F → ℂ) (hf : IsTest f') (Y : Gl r F)
    (hY : Delta (inv Y) ≠ 0) :
    IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y)) := by
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨-, hL1b, hL1c, hL1d, hL1e⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  obtain ⟨hL6a, hL6b⟩ := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  obtain ⟨-, -, -, hL4⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hC : (Cm Y).det ≠ 0 := by
    intro h0; apply hY; rw [Delta, ← hL1c Y, Matrix.det_mul, h0, zero_mul]
  have hld : (fun g : GL (Fin r) F => lastDet (act g Y)) = fun g =>
      (-1) ^ r * ((Cm Y).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) := by
    funext g; rw [hL6a, hL6b, Matrix.det_mul]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.comp₂ (hf.1.comp_continuous (continuous_act Y)) ?_ (fun a b => a * b)
    show IsLocallyConstant (fun g : GL (Fin r) F => eta (lastDet (act g Y)))
    refine isLocallyConstant_eta_comp (fun g : GL (Fin r) F => lastDet (act g Y)) ?_ ?_
    · rw [hld]
      exact continuous_const.mul (continuous_const.mul Units.continuous_coe_inv.matrix_det)
    · intro g
      rw [show lastDet (act g Y) = _ from congrFun hld g]
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hC ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit).ne_zero
  · have ha : Delta (inv (sec (inv Y))) ≠ 0 := by rw [hL1b]; exact hY
    obtain ⟨g₀, ⟨hg₀, -⟩, -⟩ := hL1e (sec (inv Y)) Y ha (hL1b _).symm
    have hS : IsCompact {h : GL (Fin r) F | act h (sec (inv Y)) ∈ tsupport f'} := by
      have := hL4 (tsupport f') {inv Y} hf.2 isCompact_singleton (by rintro b rfl; exact hY)
      convert this.image continuous_fst using 1
      ext h; constructor
      · intro hh; exact ⟨(h, inv Y), ⟨rfl, hh⟩, rfl⟩
      · rintro ⟨⟨h', a'⟩, ⟨ha', hc⟩, rfl⟩
        simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
    have hK : IsCompact {g : GL (Fin r) F | act g Y ∈ tsupport f'} := by
      have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
      convert this using 1
      ext g; simp [Homeomorph.coe_mulRight, hL1d, hg₀]
    refine HasCompactSupport.intro' hK ((isClosed_tsupport f').preimage (continuous_act Y)) ?_
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [image_eq_zero_of_notMem_tsupport hg, zero_mul]

theorem isTest_orbU_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f : Hn r F E → ℂ) (hf : IsTest f) (a : Inv r F)
    (X : Hn r F E) (ha : Delta a ≠ 0) (hX : HasInv X a) :
    IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  haveI : ContinuousStar E := ⟨by
    have : Continuous (starAddEquiv : E ≃+ E) :=
      AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1
        (fun x => by rw [starAddEquiv_apply, Unram.norm_star (F := F), one_mul])
    exact this⟩
  obtain ⟨-, -, hL5c, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, hL5iv⟩ := GlobalTheory.T.invariant_image_openClosed_local_sections F E r a ha
  obtain ⟨Ω, s, -, -, haΩ, -, hs, hprop⟩ := hL5iv ⟨X, hX⟩
  obtain ⟨g₀, hg₀, -⟩ := hL5c (s a) X a ha (hs a haΩ).2 hX
  refine ⟨hf.1.comp_continuous (continuous_actU X), ?_⟩
  have hS : IsCompact {h : Matrix.unitaryGroup (Fin r) E | actU h (s a) ∈ tsupport f} := by
    have h1 := (hprop (tsupport f) hf.2).inter_right (isClosed_univ.prod (isClosed_singleton (x := a)))
    convert h1.image continuous_fst using 1
    ext h; constructor
    · intro hh; exact ⟨(h, a), ⟨⟨haΩ, hh⟩, Set.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨h', a'⟩, ⟨⟨-, hc⟩, -, ha'⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
  have hK : IsCompact {g : Matrix.unitaryGroup (Fin r) E | actU g X ∈ tsupport f} := by
    have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
    convert this using 1
    ext g; simp [Homeomorph.coe_mulRight, actU_mul, hg₀]
  refine HasCompactSupport.intro' hK ((isClosed_tsupport f).preimage (continuous_actU X)) ?_
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  exact image_eq_zero_of_notMem_tsupport hg

end GlobalTheory.JR.OrbTest

open GlobalTheory.JR.OrbTest in

theorem GlobalTheory.JR.orb_integrand_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  intro F E _ _ _ _ _ r _
  exact ⟨fun f' hf Y hY => isTest_orbG_integrand F E r f' hf Y hY,
    fun f hf a X ha hX => isTest_orbU_integrand F E r f hf a X ha hX⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourierStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_weylElement_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  first | exact @GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | exact GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | (intros; apply GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEqStatement
section
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  first | exact @GlobalTheory.neg_one_mem_norm_of_valuation_eq | exact GlobalTheory.neg_one_mem_norm_of_valuation_eq | (intros; apply GlobalTheory.neg_one_mem_norm_of_valuation_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartOrthogonalityClasseStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCharacterOnIdempotentPart_orthogonality_classes : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), IsFrame B e π S → Finite B.Cl → ∀ (ℓ : B.A → ℝ) (h : Finset ι → ℝ), (∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) = (chi B e I x : ℝ) * h I) → ∀ I ⊆ S, ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card * h I := by
  first | exact @GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl | exact GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl | (intros; apply GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : Om l), x ∈ K0 K → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by
  first | exact @GlobalTheory.UnramValue.norm_of_mem_unramified_subfield | exact GlobalTheory.UnramValue.norm_of_mem_unramified_subfield | (intros; apply GlobalTheory.UnramValue.norm_of_mem_unramified_subfield <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), 1 ≤ j → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ (l ^ j) → ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_primitiveRoot_sub_one | exact GlobalTheory.Cyc.norm_primitiveRoot_sub_one | (intros; apply GlobalTheory.Cyc.norm_primitiveRoot_sub_one <;> assumption)
end

