import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsQuotOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPolyBase
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModThOfPres
section
noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

def RedN {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type} [Field k]
    [Algebra S.O k] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)) (N : Lats k S.n A.m) :
    Prop :=
  ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y

theorem exists_modTh_of_pres {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type}
    [Field k] [Algebra S.O k] [CharP k l] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (hC : S.CrysCalc) (hk : S.IsRes k) (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (hτ : ∀ i, (S.W H).emb (τ i) = S.emb i) (hγ : ((S.W H).χΓ γ : S.O) = 1 + (l : S.O))
    (hQ : GlobalTheory.WachUse.QN (S.W H)) :
    ∃ M : ModTh F S.D, (∀ σ, (M.ω σ : k) = algebraMap S.O k (S.Γ.ε σ)) ∧
      (∃ q : ↥S.Γ.T₀.L.T →ₗ[S.O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs S.Γ.lam q ∧ ∀ σ x, q (twistRep S.Γ.W₀ S.Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k S.G) (N : Type) [AddCommGroup N] [Module S.O N] (π : Representation S.O S.G N)
        (e : N ≃ₗ[S.O] (Fin A.m → k)), S.admitted π → (∀ σ x, e (twistRep π S.Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) →
        ∃ L, M.Model A L := by
  have hG : IsTopGal (P.PD S.K) S.emb S.D S.Γ := S.hyp.2.1
  have : FiniteDimensional ℚ_[l] ↥S.LL.1 := S.LL.2
  have : IsDiscreteValuationRing S.O := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l ↥S.LL.1
  have : IsFractionRing S.O ↥S.LL.1 := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isFractionRing_integralClosure_padicInt l ↥S.LL.1
  have hθ : IsCrysChar (P.PD S.K) S.emb S.Γ.χ₁⁻¹ (fun i => -S.D.w i) :=
    (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hG.2.1 hG.2.2.1).2
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  have hpoly : ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ),
      Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U →
      ∀ N : Lats k S.n A.m, RedN p T A q N → ∀ (i : ZMod S.n) (s : ℕ),
      (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s := by
    intro T A q U hq hK hc N hN i s hs
    exact BaseLatticeE.ePoly_base H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i s hs
  exact exists_real hθ hk hlam hC.1 hC.2.1 p.obj
    (fun T A q U hq hK hc => GlobalTheory.T.wachDeltaInvariants_reduction_isLattice H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc)
    (fun T A q U hq hK hc N hN w w' hw =>
      GlobalTheory.T.phiGamma_reduction_base_lattice_bounds H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN w w' hw)
    (fun T A q U hq hK hc N hN i x =>
      GlobalTheory.T.senMultiset_base_lattice_eq_jumps_mod H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i x)
    hpoly
    (fun T A q U hq hK hc N hN a hm ha i =>
      GlobalTheory.T.rankOne_reduction_frobeniusPullback_eq_shift H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN a hm ha i)
    (fun T A q U hq hK hc T' A' q' U' hq' hK' hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb
        N N' L hN hN' hL i =>
      GlobalTheory.Present.SumRed.reduction_sum H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc T' A' q' U' hq' hK'
        hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i)
    hG hC.2.2.1 (fun ω hω e h0 h1 => omega_pow_ne_one S k ω hω e h0 h1)

theorem real_of_presented : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (S : TopSit P), S.RealD H → GlobalTheory.WachUse.QN (S.W H) → S.CrysCalc → S.Real := by
  intro l _ P AI H _ S hR hQ hC
  unfold TopSit.Real
  intro k _ _ _ hk
  have h1 := @hR k _ _ _ hk
  obtain ⟨R, ι, hι, F, τ, γ, hτ, hγ, hp⟩ := h1
  have h2 := exists_modTh_of_pres (H := H) (S := S) (k := k) (R := R) (ι := ι) (F := F)
    (τ := τ) (γ := γ) hp.some hC hk hι hτ hγ hQ
  exact ⟨R, ι, hι, F, h2⟩

end GlobalTheory.BasePairs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetractStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residueTilt_injective_retract : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (ek : (Fq l bk.a)⟦X⟧ →+* OCb l) (pr : OCb l →+ (Fq l bk.a)⟦X⟧), (∀ s : bk.S, ek (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s) = (bk.ev s).coeff 0) ∧ Function.Injective ek ∧ (∀ a y, pr (ek a * y) = a * pr y) ∧ pr 1 = 1 := by
  first | exact @GlobalTheory.BSP.exists_resTilt_retract | exact GlobalTheory.BSP.exists_resTilt_retract | (intros; apply GlobalTheory.BSP.exists_resTilt_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulEqAcrisLatticeImageStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_eq_acrisLattice_image : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T), ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ β : TW (OCr l O) T, ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) • b = TWincl (toOB l O) T β := by
  first | exact @GlobalTheory.DenomCris.exists_smul_eq_TWincl | exact GlobalTheory.DenomCris.exists_smul_eq_TWincl | (intros; apply GlobalTheory.DenomCris.exists_smul_eq_TWincl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumOfIsCrys
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedSpan

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem exists_sum_of_isCrys [IsDomain B] (hf : GlobalTheory.RegularRing.FracInv PD)
    (hu : GlobalTheory.RegularRing.LineUnit PD) [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsCrys PD ρ) (y : V ⊗[Qp] B) :
    ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (b i)) (d i) := by
  have hs := (GlobalTheory.RegularRing.isCrys_iff_span PD hf hu ρ).1 h
  have hy : (TensorProduct.comm Qp B V).symm y ∈
      Submodule.span B (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) := hs ▸ Submodule.mem_top
  obtain ⟨m, b, e, he⟩ := Submodule.mem_span_set'.1 hy
  refine ⟨m, b, fun i => TensorProduct.comm Qp B V (e i : B ⊗[Qp] V), fun i => (e i).2, ?_⟩
  have h2 := congrArg (TensorProduct.comm Qp B V) he
  rw [LinearEquiv.apply_symm_apply, map_sum] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.Per.TiedIndep.comm_smul (LL := LL) _ _

end Generic

theorem tied_crisSpan : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ h y
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have := LL.2
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  refine exists_sum_of_isCrys (P.PD K) ?_ ?_ ρ h y
  · intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  · intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    rw [e] at hx
    exact ⟨x, by rw [Algebra.smul_def]; exact hx⟩

end GlobalTheory.Per.TiedSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateDualLocalGaloisRepAtPlace
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.TateDualX

section Mat

variable {G : Type} [Group G] {LL : Type} [Field LL] {k : ℕ} {V : Type} [AddCommGroup V] [Module LL V]

def toMat (b : Basis (Fin k) LL V) (ρ : Representation LL G V) : G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp ρ

theorem toMat_apply (b : Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) :
    toMat b ρ g = LinearMap.toMatrix b b (ρ g) := rfl

def dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) : G →* Matrix (Fin k) (Fin k) LL where
  toFun g := ((c g : LLˣ) : LL) • (M g⁻¹).transpose
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_comm]

theorem dualTw_apply (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL) (g : G) :
    dualTw c M g = ((c g : LLˣ) : LL) • (M g⁻¹).transpose := rfl

end Mat

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {k : ℕ}

theorem continuous_dualTw (c : G →* LLˣ) (M : G →* Matrix (Fin k) (Fin k) LL)
    (hc : Continuous fun g => ((c g : LLˣ) : LL)) (hM : Continuous fun g => M g) :
    Continuous fun g => dualTw c M g :=
  hc.smul (hM.comp continuous_inv).matrix_transpose

theorem continuous_toMat {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V]
    [IsModuleTopology LL V] (b : Basis (Fin k) LL V)
    (ρ : Representation LL G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    Continuous fun g => toMat b ρ g := by
  refine continuous_matrix fun a j => ?_
  have h : Continuous (b.coord a) := IsModuleTopology.continuous_of_linearMap _
  refine (h.comp (hρ (b j))).congr fun g => ?_
  simp [toMat_apply, LinearMap.toMatrix_apply]

end Cont

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {k : ℕ}

theorem isDual1_basis (b : Basis (Fin k) LL V) (ρ : Representation LL G V)
    (U : G →* Matrix (Fin k) (Fin k) LL)
    (hd : IsDual1 PD (matRep (toMat b ρ)) (matRep U) (dotProductBilin LL LL)) :
    IsDual1 PD ρ (matRep U) ((dotProductBilin LL LL).comp b.equivFun.toLinearMap) := by
  have hM : ∀ g x, b.equivFun (ρ g x) = matRep (toMat b ρ) g (b.equivFun x) := by
    intro g x
    change _ = (toMat b ρ g).mulVec _
    rw [toMat_apply, Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, ?_⟩
  · change dotProductBilin LL LL (b.equivFun (ρ g x)) (matRep U g y) = _ * dotProductBilin LL LL (b.equivFun x) y
    rw [hM]
    exact hd.1 g (b.equivFun x) y
  · have := hd.2.1 (b.equivFun x) fun y => hx y
    exact b.equivFun.injective (by rw [this, map_zero])
  · refine hd.2.2.1 y fun v => ?_
    have h := hy (b.equivFun.symm v)
    change dotProductBilin LL LL (b.equivFun (b.equivFun.symm v)) y = 0 at h
    rwa [LinearEquiv.apply_symm_apply] at h
  · rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis b, Fintype.card_fin]

end Transport

section Loc

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_cyc : Continuous fun g : Br.G D.nbr i w hw =>
    ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact hfc.comp ((GlobalTheory.Pass.FamCont.epsU_cont D.nd i).comp hι)

end Loc

theorem exists_tateDual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)),
    ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX := by
  intro D i w hw X
  have hU : Continuous fun g => dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw))
      (toMat (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ) g :=
    continuous_dualTw _ _ (continuous_cyc D i w hw) (continuous_toMat _ X.ρ X.cont)
  exact ⟨GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU, _,
    isDual1_basis (Br.PD D.loc D.nbr i w hw) (Module.finBasis (Br.LL D.nbr i w hw) X.V) X.ρ _
      (GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) _ _ fun g => dualTw_apply _ _ g)⟩

end GlobalTheory.TateDualX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatibleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K], ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) ∧ (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧ (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  first | exact @GlobalTheory.TaylorShift.shift_frob_exists | exact GlobalTheory.TaylorShift.shift_frob_exists | (intros; apply GlobalTheory.TaylorShift.shift_frob_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffWittTiltRelationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_coeff_wittTilt_relation : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {S : Type} [Fintype S] (y : S → ZMod a → A O K) (c : S → OW l O) (h : ∑ s, c s * inclO l O (ϖ.iTot t K (y s)) = 1) (τ : ZMod a), ∃ s k, ‖coeff k (y s τ : K⟦X⟧)‖ = 1 := by
  first | exact @GlobalTheory.ResidueUnitCoeff.exists_norm_coeff_eq_one | exact GlobalTheory.ResidueUnitCoeff.exists_norm_coeff_eq_one | (intros; apply GlobalTheory.ResidueUnitCoeff.exists_norm_coeff_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosed
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosedX

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem jD_aN_eq_range_gen {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}
    {s : ℕ} {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) :
    ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T a : Set (W.DD T)) =
      Set.range fun c : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (c i)) • y i := by
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T (a • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [GlobalTheory.NL.WkRange.jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • (a • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    · simp only [map_sum]
      exact Finset.sum_congr rfl fun i _ => GlobalTheory.NL.WkRange.jD_smul_letter E T _ _

theorem jD_XN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := jD_aN_eq_range_gen ((F l).E K s LL h) T ((HW l).W K s LL h).X
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosedX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpandMapDvdOfBreuilKisinFrobeniusDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory

theorem expand_map_dvd_of_frobS_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := by
  intro l hl a _ P Q hP hdvd hQ
  have hl0 : 0 < l := hl.out.pos
  set σ : Wq l a →+* Wq l a := (sigma l a : Wq l a →+* Wq l a) with hσ
  have hσinj : Function.Injective σ := (sigma l a).injective
  have hcoe : frobS l a (P : (Wq l a)⟦X⟧) =
      ((Polynomial.expand (Wq l a) l (P.map σ) : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) := by
    refine PowerSeries.ext fun n => ?_
    change PowerSeries.coeff n (PowerSeries.map σ (PowerSeries.expand l hl.out.ne_zero (P : (Wq l a)⟦X⟧))) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_expand, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_expand hl0]
    split_ifs <;> simp [Polynomial.coeff_map]
  rw [hcoe] at hQ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hmon : (Polynomial.expand (Wq l a) l (P.map σ)).Monic := (hP.map σ).expand hl0
  have hdeg : (Polynomial.expand (Wq l a) l (P.map σ)).natDegree = P.natDegree * l := by
    rw [Polynomial.natDegree_expand, Polynomial.natDegree_map_eq_of_injective hσinj]
  have H : (Polynomial.expand (Wq l a) l (P.map σ)).IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun {n} hn => by
        rw [Ideal.mem_span_singleton, Polynomial.coeff_expand hl0]
        rw [hdeg] at hn
        split_ifs with h
        · rw [Polynomial.coeff_map]
          have hlt : n / l < P.natDegree := by
            rw [Nat.div_lt_iff_lt_mul hl0]; exact hn
          obtain ⟨c, hc⟩ := hdvd _ hlt
          refine ⟨σ c, ?_⟩
          rw [hc, map_mul, map_natCast]
        · exact dvd_zero _
      monic := hmon }
  exact GlobalTheory.NB.LT.poly_dvd_of_dvd H hQ

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubring
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_mul_coeff_mem_S : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ (τ : ZMod a) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (F τ) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF τ i
  obtain ⟨w, hw, hF⟩ := hF
  have key : ∀ n, ‖coeff n ((i.factorial : K⟦X⟧) * coeff i (F τ))‖ * wS K e n =
      ‖algebraMap O K (emb t τ (w (i, n)))‖ := fun n => by
    rw [← hF τ i n, wS, ← norm_mul, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1; ring
  rw [mem_S]
  simp only [key]
  refine ⟨fun n => norm_algebraMap_le _, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt_one (K := K) l)
  have h : ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w (i, n) := by
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (f := fun n : ℕ => (i, n)) (fun _ _ _ _ h => by simpa using h)
  rw [Nat.cofinite_eq_atTop] at h
  filter_upwards [h] with n hn
  obtain ⟨c, hc⟩ := hn
  rw [Real.dist_eq, sub_zero, abs_norm, hc, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
    norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)) hr

end GlobalTheory.CrysPrism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCrystalCoordCoeffMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  first | exact @GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem | exact GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem | (intros; apply GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem <;> assumption)
end

