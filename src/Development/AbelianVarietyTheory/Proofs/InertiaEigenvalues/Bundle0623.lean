import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0364
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0585
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryOfIsAuxiliaryCharacter
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.GridCharacters

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hx' =>
  h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))

theorem expAt_succ {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w (n + 1)) (h' : ¬ χ.LevelLe w n) : ExpAt χ w (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.LamTie.GridCharacters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
section
namespace CrystallineMultiplicity
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.CharInv

theorem isCrys_and_multV_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  intro l _ P AI T K LL μ a hμ hm
  obtain ⟨h1, -, h2⟩ := GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 0
  rw [zpow_zero] at h1
  simp only [zpow_zero] at h2
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (μ g : ↥LL.1) • charRep μ⁻¹ g x :=
    fun g x => by simp [charRep]
  refine ⟨(GlobalTheory.TopSteps.CrysRules.isCrys_iff T K LL _ _ μ hρ hμ).2 h1, fun τ c => ?_⟩
  have hs := GlobalTheory.TopSteps.CrysRules.multV_shift T K LL _ _ μ hρ hμ τ (a τ)
    (fun b => by rw [hm, Multiset.count_singleton]; split_ifs <;> rfl) c
  rw [← hs, h2]
  exact if_congr (by omega) rfl rfl

end GlobalTheory.CompanionTheory.CharInv

end

end CrystallineMultiplicity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
theorem _root_.GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | exact CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | (intros; apply CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfBreuilKisinFrameIsDeRham
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isDR_of_frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsDR → Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hF
  obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨B, Q, -, hQ, -, -, hinv⟩ := GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin l K bk τ hτ C N d (fun g => (ρ g).val) F Y hF hY
  have hQ' : IsUnit (T.eD.symm.mapMatrix Q) := hQ.map T.eD.symm.mapMatrix
  refine GlobalTheory.PMon.isDR_of_periodMatrix l P (Fin d) K (Fin d → ℚ_[l]) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hQ'.unit ?_
  intro g
  have hg := hinv g
  simp only [IsUnit.unit_spec]
  ext i j
  apply T.eD.injective
  have hij := congrFun (congrFun hg i) j
  rw [LinearMap.toMatrix_eq_toMatrix']
  simp only [qRep, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, RingEquiv.mapMatrix_apply] at hij ⊢
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Units.coeHom_apply, RingHom.mapMatrix_apply, AlgEquiv.coe_toAlgHom, Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_toLin',
    Matrix.map_apply, T.actD, RingEquiv.apply_symm_apply] at ⊢
  rw [← hij]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have e : LinearMap.toMatrix' (Matrix.toLinAlgEquiv' ((algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]))) =
      (algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) :=
    LinearMap.toMatrix'_toLin' _
  erw [e]
  exact T.zD ((ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) i x)

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links

namespace GlobalTheory.LowestKType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n m : ℕ}

def kop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def sop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def Cpt (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Prop :=
  ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ)

def IsHarm (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  ∀ (τ : D.what₂.Tau) (i l : Fin m), w.p τ ≤ (i : ℕ) → (l : ℕ) < w.p τ → kop w τ i l P = 0

def IsKHw (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a P = c • P

def IsKHwMap {W : Type} [AddCommGroup W] [Module ℂ W] (w : GlobalTheory.ExportSeries.Weight D n)
    (ψ : W →ₗ[ℂ] PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b ∘ₗ ψ = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a ∘ₗ ψ = c • ψ

def IsNHw (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin n), a < b → sop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin n), sop w τ a a P = lam τ a • P

end GlobalTheory.LowestKType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverBreuilKisinCoproductInl
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrame_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A}
    (h : IsFrame bk B t p) (k : Hom B B') : IsFrame bk B' (k.f t) (k.f p) := by
  refine ⟨?_, k.f_str _ p h.2⟩
  rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ B B' k, h.1, Ideal.map_span, Set.image_singleton]

theorem env_inl_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A),
    IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  intro l _ K bk B t p hF En
  refine ⟨⟨fun m => (GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow l K bk B t p En m).flat, fun B' k => ?_⟩, GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow l K bk B t p En⟩
  obtain ⟨En'⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk B' (k.f t) (k.f p) (isFrame_map hF k)
  obtain ⟨k', hk'⟩ := GlobalTheory.T.breuilKisinPrismCoproduct_isPushout_base_change l K bk B B' t p k En En'
  exact ⟨En'.Q, k', En'.inl, hk'⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTwistRepDualOfPairing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualOne

theorem isTwistRep_dual_of_pairing {G L : Type} [Group G] [Field L]
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {V' : Type} [AddCommGroup V'] [Module L V'] [FiniteDimensional L V']
    (ρ : Representation L G V) (ρ' : Representation L G V') (χ : G →* Lˣ)
    (m : V →ₗ[L] V' →ₗ[L] L)
    (h1 : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : Lˣ) : L) * m x y)
    (h2 : ∀ y, (∀ x, m x y = 0) → y = 0) (h3 : finrank L V = finrank L V') :
    IsTwistRep χ ρ.dual ρ' := by
  have hinj : Function.Injective m.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y fun x => by simpa using LinearMap.congr_fun hy x
  have hdim : finrank L V' = finrank L (Module.Dual L V) := by
    rw [Subspace.dual_finrank_eq, h3]
  let f : V' ≃ₗ[L] Module.Dual L V := m.flip.linearEquivOfInjective hinj hdim
  have hf : ∀ y x, f y x = m x y := fun y x => rfl
  refine ⟨f.symm, fun g φ => ?_⟩
  obtain ⟨y, rfl⟩ := f.surjective φ
  apply f.injective
  rw [map_smul, f.apply_symm_apply, f.symm_apply_apply]
  ext x
  have hx : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := h1 g (ρ g⁻¹ x) y
  rw [hx] at this
  rw [hf, this, LinearMap.smul_apply, Representation.dual_apply, smul_eq_mul]
  congr 1

theorem isCrys_of_isDual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) ρ ρ' m → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' := by
  intro l _ P AI hT K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m hD hρ
  obtain ⟨h1, -, h2, h3⟩ := hD
  have htw := isTwistRep_dual_of_pairing ρ ρ' _ m h1 h2 h3
  have hreg := (GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT).1
  have hdual := GlobalTheory.Per.TiedDual.tied_isCrys_dual l P AI hT hreg K LL V ρ hρ
  have hcyc := (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI hT K LL 1).1
  rw [zpow_one] at hcyc
  exact (GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift l P AI hT K LL _ ρ.dual V' ρ' _ htw hcyc hdual).1

end GlobalTheory.DualOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_saturated_basis_etale_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  first | exact @GlobalTheory.EtaleLattice.isUnit_saturated_basis | exact GlobalTheory.EtaleLattice.isUnit_saturated_basis | (intros; apply GlobalTheory.EtaleLattice.isUnit_saturated_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL) (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L), ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  first | exact @GlobalTheory.BKGal.PackMap.main | exact GlobalTheory.BKGal.PackMap.main | (intros; apply GlobalTheory.BKGal.PackMap.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) → (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) → Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧ locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  first | (exact @GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (exact GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (intros; apply GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateDcrisFrobeniusEigen
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PZ.ColmezVec

theorem ev_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    PowerSeries.constantCoeff L = 0 → PowerSeries.coeff 1 L = 1 → ∀ (x : AK K), thetaK K x = 0 → x ≠ 0 →
    ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y → y ≠ 0 := by
  intro l _ K L hL h0 h1 x hx hx0 y hy e
  obtain ⟨L', u, hL', hc, hu, hyu⟩ := GlobalTheory.T.evaluation_power_series_shift l K L hL x hx y hy
  obtain ⟨L'', u', -, -, -, hu'⟩ := GlobalTheory.T.evaluation_power_series_shift l K L' hL' x hx u hu
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.theta_extension_to_complete l K
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero, zero_add, e] at hyu
  have h2 := congrArg ψ hu'
  rw [GlobalTheory.T.period_ring_no_zero_divisors l K x hx0 u hyu.symm, hc, zero_add, h1, map_zero, map_one, map_add, map_one, map_mul, hψ, hx] at h2
  simp at h2

theorem exists_period (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l)
    (h : LTData K χ π z) : ∃ t : GlobalTheory.AcrisK.BK K, t ≠ 0 ∧ frobB K t = inK K (π : ↥K.1) * t ∧
      ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  obtain ⟨hπ, hF, v, hv0, hv1, hv, hg⟩ := GlobalTheory.T.lubin_tate_torsion_sequence l K χ π z h
  have hπu := GlobalTheory.LTTilt.not_isUnit_intToOC K hπ
  have hcomp : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ Ideal.span {intToOC K π} := fun n =>
    Ideal.mem_span_singleton.2 ⟨-v (n + 1), by rw [← hv n]; ring⟩
  obtain ⟨x, hx, -⟩ := GlobalTheory.LTTilt.existsUnique_isTiltOf (fK K) (NeZero.pos _) (intToOC K π) hπu
    (GlobalTheory.LTTilt.natCast_mem_span_intToOC K hπ) v hcomp
  obtain ⟨ω₀, hred, hω₀⟩ := GlobalTheory.T.exists_frobenius_lift_lubin_tate l K π hπ x
  choose r hr using (frobq_bijective K).2
  let ω : ℕ → AK K := fun n => r^[n] ω₀
  have hch : ∀ n, frobq K (ω (n + 1)) = ω n := fun n => by
    simp only [ω, Function.iterate_succ_apply', hr]
  have hθ : ∀ n, thetaK K (ω n) = v n := GlobalTheory.T.theta_of_tilt_compatible_sequence l K π hπ v ω hv (hred ▸ hx) hch hω₀
  have h0 : thetaK K ω₀ = 0 := (hθ 0).trans hv0
  have hne : ω₀ ≠ 0 := fun e => hv1 (by
    have : ω 1 = 0 := (frobq_bijective K).1 (by rw [hch, map_zero]; exact e)
    rw [← hθ, this, map_zero])
  have hker : ∀ (M : ℕ) (y : AK K), ω₀ ^ M ∣ y → y ∈ RingHom.ker (thetaK K) ^ M := fun M y ⟨c, hc⟩ =>
    hc ▸ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (show ω₀ ∈ RingHom.ker (thetaK K) from h0) M)
  have hev := ev_ltLog hπ hF ω₀ h0
  refine ⟨ltLog hπ hF ω₀ h0, ev_ne_zero l K _ (onDisc_log hπ hF) (GlobalTheory.LTLog.constantCoeff_log _ hπ hF)
    (GlobalTheory.LTLog.coeff_one_log _ hπ hF) ω₀ h0 hne _ hev, ?_, fun g => ?_⟩
  · refine ev_log_self hπ hF h0 (fun n => hker n _ ?_) hev.frob
    have hq : resCard K = l ^ fK K := rfl
    have e : ∀ j, inO K (PowerSeries.coeff j (ltSeries K π)) * ω₀ ^ j =
        (if j = 1 then inO K π * ω₀ ^ j else 0) + if j = l ^ fK K then ω₀ ^ j else 0 := fun j => by
      rw [ltSeries, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, hq]
      split_ifs <;> simp [add_mul]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, hω₀]
    rw [add_sub_add_comm]
    refine dvd_add ?_ ?_
    · split_ifs with h1
      · simp
      · rw [sub_zero]
        exact Dvd.dvd.mul_left (by simpa using pow_dvd_pow ω₀ (not_lt.1 h1)) _
    · split_ifs with h1
      · simp
      · rw [sub_zero]
        exact pow_dvd_pow ω₀ (not_lt.1 h1)
  · obtain ⟨a, ha, hs⟩ := hg g
    obtain ⟨y, hy1, hy2, hy3⟩ := GlobalTheory.T.exists_compatible_power_series_value l K ω (lubinTateHom hπ hF hF a).toPowerSeries
      (fun n => Per.σO (g : GQ l) (v n)) hch
      (fun n => by rw [hθ]; exact GlobalTheory.LTTilt.norm_lt_one_of_compat K hπ hcomp hv0 n)
      (fun n => by rw [hθ]; exact hs n)
    have hy : gal K g ω₀ = y 0 := sub_eq_zero.1 (GlobalTheory.T.frobenius_compatible_theta_zero l K (fun n => gal K g (ω n) - y n)
      (fun n => by rw [map_sub, hy1, ← gal_frobq, hch])
      (fun n => by rw [map_sub, hy2, thetaK_gal, hθ, sub_self]))
    rw [← ha]
    exact ev_log_hom hπ hF a h0 (fun n => hker n _ (hy ▸ hy3 n)) (hev.gal g)

section Abstract

variable {G : Type} [Group G] {Q K₀ K : Type} [Field Q] [Field K₀] [Field K]
    [Algebra Q K₀] [Algebra Q K] [Algebra K₀ K] [IsScalarTower Q K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Q B] [Algebra K₀ B] [IsScalarTower Q K₀ B]
    [Algebra Q BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Q K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Q K₀ BdR]
    (PD : PeriodData G Q K₀ K B BdR)

theorem pow_phi_algebraMap (k : ℕ) (c : K₀) : (PD.φ ^ k) (algebraMap _ B c) = algebraMap _ B ((⇑PD.σ)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, ih, PD.φ_K₀, Function.iterate_succ_apply']

def phiPow (f : ℕ) (hσ : ∀ c, (⇑PD.σ)^[f] c = c) : B →ₐ[K₀] B where
  toRingHom := (PD.φ ^ f).toRingHom
  commutes' := fun c => (pow_phi_algebraMap PD _ c).trans (congrArg _ (hσ c))

end Abstract

theorem ext_BK {l : ℕ} [Fact l.Prime] {K : FinExt l} {S : Type} [CommRing S] (u v : GlobalTheory.AcrisK.BK K →+* S)
    (hK : ∀ c, u (inK K c) = v (inK K c)) (hA : ∀ a, u (toB K (inC K a)) = v (toB K (inC K a))) : u = v := by
  refine ringHom_extB fun c => ?_
  refine RingHom.congr_fun (GlobalTheory.AcrisK.ringHom_ext (u := u.comp (toB K)) (v := v.comp (toB K)) hA fun c => ?_) c
  simp only [RingHom.comp_apply, ← inK_oK, hK]

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K : FinExt l)

theorem pow_phi_acris (k : ℕ) (a : Per.Acris l) :
    ((P.PD K).φ ^ k) (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) ((⇑(phiA l))^[k] a)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, Function.iterate_succ_apply', P.PD_φ]
    apply T.eB.injective
    rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← plusToB_alg, ← plusToB_alg,
      ← plusToB_phi, phiP_alg]

theorem act_acris (g : ↥(GK K)) (a : Per.Acris l) :
    (P.PD K).actB g (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) a)) := by
  apply T.eB.injective
  rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← plusToB_alg, ← plusToB_alg,
    ← plusToB_sig, sigP_alg]

end Tied

end GlobalTheory.PZ.ColmezVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOne
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

theorem norm_prod_sat_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ : CG E a)
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  intro E _ _ _ a σ w B hu hB
  obtain ⟨ω, hωu, hω⟩ := hu
  induction σ using Quotient.inductionOn with | _ π => ?_
  change GlobalTheory.LFun.HasSatGL w (π.locRep w) B at hB
  change π.HasCentChar ω at hω
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let u : (w.adicCompletion E)ˣ := Units.mk0 ϖ hϖ0
  let S : GL (Fin a) (w.adicCompletion E) := Matrix.GeneralLinearGroup.scalar (Fin a) u
  let K := GlobalTheory.LFun.KGL w a
  have hS : ((S : GL (Fin a) (w.adicCompletion E)) : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = diagJ a ϖ a := by
    ext i j
    simp [S, u, diagJ, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  have hT : Tj ℂ a (Ov E w) ϖ a = dosetInd ℂ K S := by
    unfold Tj dosetInd
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    refine exists_congr fun y => and_congr_right fun _ => exists_congr fun z => and_congr_right fun _ => ?_
    rw [Units.ext_iff, Units.val_mul, Units.val_mul, hS]
  have hc : ∀ g ∈ DoubleCoset.doubleCoset S (K : Set _) K, ∃! γ, γ ∈ ({S} : Finset _) ∧ γ⁻¹ * g ∈ K := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨S, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have e : S⁻¹ * (y * S * z) = y * z := by
      rw [show y * S = S * y from (scalar_comm u y).symm]; group
    rw [e]
    exact K.mul_mem hy hz
  have hR : ∀ γ ∈ ({S} : Finset _), γ ∈ DoubleCoset.doubleCoset S (K : Set _) K := by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, 1, K.one_mem, by group⟩
  have h1 := hx.2.2.2 ϖ hϖ a le_rfl
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx.2.1 hR hc, Finset.sum_singleton] at h1
  have h2 : π.locRep w S x = ((ω.1 (finId E (Units.map (corner (sLoc E w)) u)) : ℂˣ) : ℂ) • x := by
    have e : locGL E a w S = Matrix.GeneralLinearGroup.scalar (Fin a) (Units.map (corner (sLoc E w)) u) :=
      cornerGL_scalar (sLoc E w) u
    change π.finPart (locGL E a w S) x = _
    rw [e]
    exact hω _ x
  rw [h2] at h1
  have h3 := smul_left_injective ℂ hx.1 h1
  have hcard : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
  have h4 : GlobalTheory.LFun.satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    rw [GlobalTheory.LFun.satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul, Multiset.esymm, ← hcard,
      Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [← h4, ← h3]
  exact hωu _

end GlobalTheory.RSNonvan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricSublevel_finiteIndex_more_places : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (levEnv V β { L with Q := Q', xq := xq }).J ≤ (levEnv V β L).J ∧ (levEnv V β { L with Q := Q', xq := xq }).Q ≤ (levEnv V β L).Q ∧ (((levEnv V β { L with Q := Q', xq := xq }).J).subgroupOf (levEnv V β L).J).FiniteIndex ∧ ∀ g : Bridge.Gf V, g ∈ (levEnv V β { L with Q := Q', xq := xq }).Q → g ∈ (levEnv V β L).J → g ∈ (levEnv V β { L with Q := Q', xq := xq }).J := by
  first | exact @GlobalTheory.sublevel_finiteIndex | exact GlobalTheory.sublevel_finiteIndex | (intros; apply GlobalTheory.sublevel_finiteIndex <;> assumption)
end

