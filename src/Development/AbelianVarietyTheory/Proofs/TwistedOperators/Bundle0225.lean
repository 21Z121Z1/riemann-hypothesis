import Mathlib
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommonKernelCommutingNilpotent
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory

noncomputable def jointNullChain {V : Type} [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V)
    (S : Submodule ℂ V) : ℕ → Submodule ℂ V
  | 0 => S
  | m + 1 => jointNullChain T S m ⊓ LinearMap.ker (T m)

theorem exists_common_null_of_commute_locallyNilpotent :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V) (S : Submodule ℂ V),
      FiniteDimensional ℂ S → S ≠ ⊥ → (∀ k, ∀ v ∈ S, T k v ∈ S) →
      (∀ k l, Commute (T k) (T l)) → (∀ k, ∀ v ∈ S, ∃ N : ℕ, (T k ^ N) v = 0) →
      ∃ v ∈ S, v ≠ 0 ∧ ∀ k, T k v = 0 := by
  intro V _ _ T S hfin hne hstab hcomm hnil
  set Z := jointNullChain T S with hZ
  have hsucc : ∀ m, Z (m + 1) = Z m ⊓ LinearMap.ker (T m) := fun m => rfl
  have hanti : Antitone Z := antitone_nat_of_succ_le (fun m => by rw [hsucc]; exact inf_le_left)
  have hleS : ∀ m, Z m ≤ S := fun m => hanti (Nat.zero_le m)
  have hst : ∀ m l, ∀ v ∈ Z m, T l v ∈ Z m := by
    intro m
    induction m with
    | zero => exact fun l v hv => hstab l v hv
    | succ m ih =>
      intro l v hv
      rw [hsucc] at hv ⊢
      refine ⟨ih l v hv.1, ?_⟩
      have h0 : T m v = 0 := hv.2
      show T m (T l v) = 0
      have := LinearMap.congr_fun (hcomm m l).eq v
      simp only [Module.End.mul_apply] at this
      rw [this, h0, map_zero]
  have hstpow : ∀ m l i, ∀ v ∈ Z m, (T l ^ i) v ∈ Z m := by
    intro m l i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hst m l _ (ih v hv)
  have hkill : ∀ m, ∀ k < m, ∀ v ∈ Z m, T k v = 0 := by
    intro m
    induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      intro k hk v hv
      rw [hsucc] at hv
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact ih k hk v hv.1
      · subst hk; exact hv.2
  have hnebot : ∀ m, Z m ≠ ⊥ := by
    intro m
    induction m with
    | zero => exact hne
    | succ m ih =>
      obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp ih
      have hex : ∃ N : ℕ, (T m ^ N) w = 0 := hnil m w (hleS m hw)
      classical
      set N0 := Nat.find hex with hN0
      have hN0spec : (T m ^ N0) w = 0 := Nat.find_spec hex
      have hN0pos : N0 ≠ 0 := by
        intro h
        rw [h, pow_zero, Module.End.one_apply] at hN0spec
        exact hw0 hN0spec
      obtain ⟨i, hi⟩ : ∃ i, N0 = i + 1 := ⟨N0 - 1, by omega⟩
      have hne0 : (T m ^ i) w ≠ 0 := Nat.find_min hex (by omega)
      rw [Submodule.ne_bot_iff]
      refine ⟨(T m ^ i) w, ?_, hne0⟩
      rw [hsucc]
      refine ⟨hstpow m m i w hw, ?_⟩
      show T m ((T m ^ i) w) = 0
      rw [← Module.End.mul_apply, ← pow_succ', ← hi, hN0spec]
  have hfinZ : ∀ m, FiniteDimensional ℂ (Z m) := fun m => Submodule.finiteDimensional_of_le (hleS m)
  let f : ℕ → ℕ := fun m => Module.finrank ℂ (Z m)
  have hexc : ∃ c, ∃ m, f m = c := ⟨_, 0, rfl⟩
  classical
  obtain ⟨M, hM⟩ := Nat.find_spec hexc
  have hmin : ∀ m, Nat.find hexc ≤ f m := fun m => Nat.find_min' hexc ⟨m, rfl⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp (hnebot M)
  refine ⟨w, hleS M hw, hw0, fun k => ?_⟩
  rcases lt_or_ge k M with hk | hk
  · exact hkill M k hk w hw
  · have hle : Z (k + 1) ≤ Z M := hanti (by omega)
    have heq : Z (k + 1) = Z M := by
      haveI := hfinZ M
      apply Submodule.eq_of_le_of_finrank_eq hle
      have h1 := hmin (k + 1)
      have h2 : f (k + 1) ≤ f M := Submodule.finrank_mono hle
      have h3 : f M = Nat.find hexc := hM
      show f (k + 1) = f M
      omega
    exact hkill (k + 1) k (Nat.lt_succ_self k) w (heq ▸ hw)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletionTensorAllRootsMapBijectiveCm
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

theorem subring_pi_mem_of_const_of_injective {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring (ι → ℂ))
    (hc : ∀ c : ℂ, (fun _ => c) ∈ R) (a : ι → ℂ) (ha : Function.Injective a) (haR : a ∈ R) (x : ι → ℂ) :
    x ∈ R := by
  have hp : ∀ p : ℂ[X], (fun i => p.eval (a i)) ∈ R := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have := R.add_mem hp hq
      convert this using 1
      ext i; simp
    | monomial n c =>
      have := R.mul_mem (hc c) (R.pow_mem haR n)
      convert this using 1
      ext i; simp [eval_monomial]
  have := hp (Lagrange.interpolate Finset.univ a x)
  convert this using 1
  ext i
  exact (Lagrange.eval_interpolate_at_node x ha.injOn (Finset.mem_univ i)).symm

theorem exists_extensionEmbedding_eq_ofReal {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsReal) (t : ℝ) : ∃ a : w.Completion, InfinitePlace.Completion.extensionEmbedding w a = (t : ℂ) := by
  refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t, ?_⟩
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem PsiAll_surjective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} [IsTotallyComplex E] {r : ℕ} (P : PPol σ r) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) : Function.Surjective (PsiAll P τ) := by
  intro x
  have hτ : ¬ ComplexEmbedding.IsReal τ.1 := IsTotallyComplex.complexEmbedding_not_isReal τ.1
  have : ∃ e : E, (τ.1 e).im ≠ 0 := by
    by_contra h
    push_neg at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext e
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (h e)
  obtain ⟨e, he⟩ := this
  refine subring_pi_mem_of_const_of_injective (PsiAll P τ).range ?_ (cxRoots τ.1 P) (cxRoots_injective P τ) ?_ x
  · intro c
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal hw (c.re - c.im / (τ.1 e).im * (τ.1 e).re)
    obtain ⟨b, hb⟩ := exists_extensionEmbedding_eq_ofReal hw (c.im / (τ.1 e).im)
    refine ⟨a ⊗ₜ[F] 1 + b ⊗ₜ[F] algebraMap E (Fld P) e, ?_⟩
    ext i : 1
    rw [PsiAll_apply, map_add, Psi_tmul, Psi_tmul, psiL_algebraMap, map_one, ha, hb, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  · refine ⟨1 ⊗ₜ[F] alpha P, ?_⟩
    ext i : 1
    rw [PsiAll_apply, Psi_tmul, psiL_alpha, map_one, one_mul]

theorem PsiAll_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  intro F E _ _ _ _ _ σ hCM r P w τ
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTotallyComplex E := hCM.2.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hs := PsiAll_surjective P hw τ
  refine ⟨?_, hs⟩
  letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
  let f : w.Completion ⊗[F] Fld P →ₗ[w.Completion] (Fin r → ℂ) :=
    { toFun := PsiAll P τ
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]
        ext i
        rw [Pi.mul_apply, PsiAll_apply, Psi_tmul, map_one, mul_one, Pi.smul_apply, Algebra.smul_def]
        rfl }
  have hk : Module.finrank w.Completion ℂ = 2 := by
    rw [Algebra.finrank_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (RingEquiv.refl ℂ) ?_,
      Complex.finrank_real_complex]
    ext x
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x
  haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite E (Fld P) := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finite
  haveI : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)
  have hd : Module.finrank w.Completion (w.Completion ⊗[F] Fld P) = Module.finrank w.Completion (Fin r → ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank F E (Fld P), h2, finrank_Fld,
      Module.finrank_pi_fintype]
    simp [hk, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) hd).2 hs

end GlobalTheory.TrEll.RealTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Matrix
namespace GlobalTheory.KapLevel

theorem cast_one_fin {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (k : I'.Gf) (hk : k ∈ I'.Kset) :
    ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).1 = 1 ∧
      ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).2 ∈ I.Kset := by
  subst e
  exact ⟨rfl, hk⟩

theorem lat_eq (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
  rw [Formalism.L2.SG.InstExistsPf.Lv_eq_map]
  rfl

theorem hatL_eq (D : D7) :
    (Formalism.IndefR.RationalEmbedding.inst D).Lf = Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  show Formalism.MainNotions.S.lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) = _
  rw [Formalism.MainNotions.S.Inh.aut_lamAf_eq, lat_eq]
  rfl

theorem kset_stab {D : D7} (x : (Formalism.IndefR.RationalEmbedding.inst D).Gf) (hx : x ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset)
    (g : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (hg : g = x.1) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) ∧
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  subst hg
  have h0 : x.1 ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := hx
  have h1 : x.1⁻¹ ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := (Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf).inv_mem h0
  have e := SetLike.ext_iff.1 (hatL_eq D)
  refine ⟨fun y hy => (e _).1 ((h0 y).1 ((e y).2 hy)), fun y hy => (e _).1 ((h1 y).1 ((e y).2 hy))⟩

theorem st_of_stab {D : D7} (g ft β : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D))
    (hF : Formalism.L2.DIV.IsFrame (ft * β) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h0 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) :
    ft⁻¹ * g * ft ∈ Formalism.L2.DIV.St β := by
  have hS : g ∈ Formalism.L2.DIV.St (ft * β) := (GlobalTheory.LevSplit.mem_St_iff (ft * β) _ hF g).2 ⟨h0, h1⟩
  obtain ⟨z, hz⟩ := hS
  refine ⟨z, ?_⟩
  rw [← hz]
  show β * Formalism.L2.DIV.intGL _ _ _ z * β⁻¹ = ft⁻¹ * ((ft * β) * Formalism.L2.DIV.intGL _ _ _ z * (ft * β)⁻¹) * ft
  group

theorem kap_mem_parLev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, kap X h t k ∈ GfC (Yc D 0) ∧ finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t _ _ _ ht _ hF k hk
  obtain ⟨hy1, hy2⟩ := cast_one_fin h.symm k hk
  have hkap : kap X h t k = (@id (GA D (D.sp.Y 0)) t)⁻¹ * (Formalism.IndefR.RationalEmbedding.iota D).symm
      ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)) * @id (GA D (D.sp.Y 0)) t := rfl
  refine ⟨?_, ?_⟩
  · rw [hkap]
    exact mul_mem (mul_mem (inv_mem ht) ((Formalism.L2.SG.EvalTIota.brg_mem_GfC_i _).2 hy1)) ht
  · have hU := GlobalTheory.LevSplit.finE_mem_UA (Yc D 0) (kap X h t k)
    have hfin0 : Formalism.IndefR.Lev.finE (D.sp.Y 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (D.sp.Y 0) t)⁻¹ *
        @id (GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (D.sp.Y 0) t := by
      rw [hkap, map_mul, map_mul, map_inv, Formalism.L2.SG.EvalTIota.finE_brg_i]
      rfl
    have hfin : Formalism.IndefR.Lev.finE (Yc D 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹ *
        @id (GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (Yc D 0) t := hfin0
    rw [hfin] at hU ⊢
    obtain ⟨s0, s1⟩ := kset_stab _ hy2 _ rfl
    have hr : ∀ a : Fin (Yc D 0).rank, (a : ℕ) < (R.dat0 R.triv).r := fun a =>
      lt_of_lt_of_eq a.2 (Formalism.L2.SG.InstExistsPf.rank_eq D)
    refine Formalism.L2.DIV.mem_parLev.2 ⟨hU, st_of_stab _ _ _ hF s0 s1, fun PP _ => ?_, fun PP hP => ?_⟩
    · rw [Formalism.L2.DIV.mem_blockTri]
      intro i j hij
      exfalso
      unfold Formalism.L2.DIV.blkOf at hij
      rw [if_pos (hr i), if_pos (hr j)] at hij
      exact lt_irrefl 0 hij
    · exact absurd hP (Finset.notMem_empty PP)

end GlobalTheory.KapLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantPairingUniqueUpToScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairingLine

open GlobalTheory.PairingTensor

theorem exists_tensor {V A B H₁ H₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂) (h₁ : Function.Injective i₁)
    (h₂ : Function.Injective i₂) (φ : B → V →ₗ[ℂ] A)
    (hadj : ∀ P x, ∃ b, ∀ y, ⟪i₁ x, i₁ (φ y P)⟫_ℂ = ⟪i₂ y, i₂ b⟫_ℂ)
    (hE : ∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) :
    ∃ f : V →ₗ[ℂ] A ⊗[ℂ] B, (∀ P y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) (f P) = φ y P) ∧
      ∀ z w : A ⊗[ℂ] B,
        (∀ y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) z = contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) w) → z = w := by
  let m : B → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ (i₂ y)) ∘ₗ i₂
  have hm : ∀ y b, m y b = inner ℂ (i₂ y) (i₂ b) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => by
    apply h₂
    rw [map_zero]
    exact inner_self_eq_zero.mp (h b)
  have sepR : ∀ z w : A ⊗[ℂ] B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  choose ψ hψ using hadj
  have ex : ∀ P, ∃ z : A ⊗[ℂ] B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ P (a j), fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
    rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, hm, ← hψ, ha]
  choose g hg using ex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sepR _ _ fun y => by rw [map_add, hg, hg, hg, map_add]
           map_smul' := fun s P => sepR _ _ fun y => by
             rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }, hg, sepR⟩

theorem contrR_map_right {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : A ⊗[ℂ] B) :
    contrR m (TensorProduct.map LinearMap.id b z) = contrR (m ∘ₗ b) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem contrR_neg {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (z : A ⊗[ℂ] B) : contrR (-m) z = -contrR m z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

theorem linear_eq_of_upq {p q : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (F G : Mat p q →ₗ[ℂ] N)
    (h : ∀ Z ∈ upq p q, F Z = G Z) (Z : Mat p q) : F Z = G Z := by
  have e1 := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have e2 := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hd := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = X at e1 hd
  generalize Complex.I • (Z - conjR Z) = Y at e2 hd
  subst hd
  simp only [map_add, map_smul, e1, e2]

theorem skew {p q : ℕ} {T : GrpData p q} (R : DSRep T) {Y : Mat p q} (hY : Y ∈ upq p q) (x y : R.HK.V) :
    ⟪R.ι (R.HK.act Y x), R.ι y⟫_ℂ = -⟪R.ι x, R.ι (R.HK.act Y y)⟫_ℂ := by
  have h1 := (R.der Y hY x).inner ℂ (R.der Y hY y)
  simp only [GlobalTheory.RealPar.DerivedAdjoint.inner_map, zero_smul, T.expt_zero, map_one,
    ContinuousLinearMap.one_apply] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (R.ι x) (R.ι y)))
  linear_combination h2

theorem exists_intw {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (hA : Formalism.MainNotions.SchurIrreducible.AdmGK R₁.HK) (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V)
    (hB : CoverW R₁ R₂ B) :
    ∃ f : Pol p q r s →ₗ[ℂ] R₁.HK.V ⊗[ℂ] R₂.HK.V,
      (∀ Z, f ∘ₗ fockAct1 p q r s Z = TensorProduct.map (R₁.HK.act Z) LinearMap.id ∘ₗ f) ∧
      (∀ Z, f ∘ₗ fockAct2 p q r s Z = TensorProduct.map LinearMap.id (R₂.HK.act Z) ∘ₗ f) ∧
      ∀ P y, contrR (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) (f P) = B P y := by
  have hsrc : ∀ Z P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y) := fun Z P y =>
    linear_eq_of_upq (B.flip y ∘ₗ (fockAct1 p q r s).flip P) (R₁.HK.act.flip (B P y))
      (fun Z hZ => hB.src Z hZ P y) Z
  have hlie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1
  obtain ⟨f, hf, sep⟩ := exists_tensor R₁.ι R₂.ι R₁.ι_inj R₂.ι_inj (fun y => B.flip y) hB.adj (fun P => by
    obtain ⟨W, hW, hP, hst⟩ := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).1
    obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R₁.HK hA _ (fockAct1 p q r s) (fun Y Z _ _ => hlie Y Z) W hW hst
      (fun v _ => ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 v).2)
    exact ⟨E, hE, fun y => hE' (B.flip y) (fun Z _ v => hsrc Z v y) P hP⟩)
  simp only [LinearMap.flip_apply] at hf
  refine ⟨f, fun Z => ?_, fun Z => ?_, hf⟩
  · refine LinearMap.ext fun P => sep _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, hsrc]
  · refine LinearMap.ext fun P => ?_
    refine linear_eq_of_upq (f ∘ₗ (fockAct2 p q r s).flip P)
      (((LinearMap.lTensorHom R₁.HK.V).comp R₂.HK.act).flip (f P)) (fun Z hZ => ?_) Z
    refine sep _ _ fun y => ?_
    change contrR _ (f (fockAct2 p q r s Z P)) = contrR _ (TensorProduct.map LinearMap.id (R₂.HK.act Z) (f P))
    have e : (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) ∘ₗ R₂.HK.act Z = -(innerₛₗ ℂ (R₂.ι (R₂.HK.act Z y)) ∘ₗ R₂.ι) := by
      refine LinearMap.ext fun b => ?_
      change ⟪R₂.ι y, R₂.ι (R₂.HK.act Z b)⟫_ℂ = -⟪R₂.ι (R₂.HK.act Z y), R₂.ι b⟫_ℂ
      rw [skew R₂ hZ, neg_neg]
    rw [contrR_map_right, e, contrR_neg, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB.tgt Z hZ P y)

theorem pairing_line : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds p q lam).HK → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → ∃ B₀ : Pol p q r s → (X.ds r s lam').HK.V → (X.ds p q lam).HK.V, ∀ B : Pol p q r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] (X.ds p q lam).HK.V, CoverW (X.ds p q lam) (X.ds r s lam') B → ∃ c : ℂ, ∀ P y, B P y = c • B₀ P y := by
  intro X p q r s lam lam' hA hL
  obtain ⟨f₀, -, -, hf₀⟩ := hL
  refine ⟨fun P y => contrR (innerₛₗ ℂ ((X.ds r s lam').ι y) ∘ₗ (X.ds r s lam').ι) (f₀ P), fun B hB => ?_⟩
  obtain ⟨f, h1, h2, hf⟩ := exists_intw _ _ hA B hB
  obtain ⟨c, hc⟩ := hf₀ f ⟨h1, h2⟩
  refine ⟨c, fun P y => ?_⟩
  rw [← hf, hc, LinearMap.smul_apply, map_smul]

end GlobalTheory.PairingLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords
section
open scoped InnerProductSpace

namespace GlobalTheory.TraceCycWord

theorem etr_succ_eq_sum_cycWord : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ),
    Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  intro A _ n E m
  rw [GlobalTheory.PhiEigenfun.sum_cycWord, Formalism.REAL.etr]
  exact Finset.sum_congr rfl fun c _ => GlobalTheory.PhiEigenfun.epow_eq E (m + 1) c c

end GlobalTheory.TraceCycWord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdjoinRootLinearEquivOfCharpolyEqStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E), A.charpoly = P.1 → ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by
  first | exact @GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | exact GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | (intros; apply GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFockStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_contraction_isometric_discreteSeries_fock : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  first | exact @GlobalTheory.Chain.CoverContr.exists_isCoverIt | exact GlobalTheory.Chain.CoverContr.exists_isCoverIt | (intros; apply GlobalTheory.Chain.CoverContr.exists_isCoverIt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  first | exact @GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | exact GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | (intros; apply GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum <;> assumption)
end

