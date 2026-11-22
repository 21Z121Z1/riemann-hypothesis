import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOffStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_commute_of_one_off : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : GlobalTheory.CellDec.abelian₂ E n S) (p : GA E n),
    (∀ w ∉ S, Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1) →
    p * GlobalTheory.CellDec.tl n ϖ l.1 = GlobalTheory.CellDec.tl n ϖ l.1 * p := by
  first | exact @GlobalTheory.CellDec.TlComm.tl_commute_of_one_off | exact GlobalTheory.CellDec.TlComm.tl_commute_of_one_off | (intros; apply GlobalTheory.CellDec.TlComm.tl_commute_of_one_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonalStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ)),
    (∀ w i, ((l' w i : ℕ) : ℤ) = l w i) → GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  first | exact @GlobalTheory.CellDecNat.tl_eq_jsw_tl | exact GlobalTheory.CellDecNat.tl_eq_jsw_tl | (intros; apply GlobalTheory.CellDecNat.tl_eq_jsw_tl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalInertiaEqZeroPotSemistableDieudonne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

open GlobalTheory.Pst GlobalTheory.Pst.LetterDim GlobalTheory.WeilDeligne TensorProduct Module

namespace GlobalTheory.IneKillsDpst

section General

variable {L U D : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* Module.End L D)

def Kills {F : Type} [Field F] (s : L →+* F) (τ : U →+* F) (T : D → D) : Prop :=
  ∀ f ∈ letterHom m s τ, ∀ y, f (T y) = 0

theorem kills_comp {F F' : Type} [Field F] [Field F'] (g : F ≃+* F') (s : L →+* F) (τ : U →+* F)
    (s' : L →+* F') (τ' : U →+* F') (hs : ∀ a, g (s a) = s' a) (hτ : ∀ a, g (τ a) = τ' a) (T : D → D)
    (h : Kills m s τ T) : Kills m s' τ' T := by
  intro f hf y
  let f0 : D →+ F := g.symm.toAddMonoidHom.comp f
  have hf0 : f0 ∈ letterHom m s τ :=
    ⟨fun a x => by simp [f0, hf.1, ← hs], fun c x => by simp [f0, hf.2, ← hτ]⟩
  have := h f0 hf0 y
  simpa [f0] using this

theorem kills_comp_iff {F F' : Type} [Field F] [Field F'] (g : F ≃+* F') (s : L →+* F) (τ : U →+* F)
    (s' : L →+* F') (τ' : U →+* F') (hs : ∀ a, g (s a) = s' a) (hτ : ∀ a, g (τ a) = τ' a) (T : D → D) :
    Kills m s τ T ↔ Kills m s' τ' T :=
  ⟨kills_comp m g s τ s' τ' hs hτ T, kills_comp m g.symm s' τ' s τ
    (fun a => by rw [← hs, RingEquiv.symm_apply_apply]) (fun a => by rw [← hτ, RingEquiv.symm_apply_apply]) T⟩

theorem kills_frob {F : Type} [Field F] (φ : Module.End L D) (hφ : Function.Bijective φ) (σ : U → U)
    (hσ : ∀ c, φ * m c = m (σ c) * φ) (hσ' : Function.Surjective σ) (s : L →+* F) (τ τ' : U →+* F)
    (hτ : ∀ c, τ' c = τ (σ c)) (T : D → D) (hT : ∀ y, φ (T y) = T (φ y)) :
    Kills m s τ T ↔ Kills m s τ' T := by
  have h1 : ∀ c x, φ (m c x) = m (σ c) (φ x) := fun c x => LinearMap.congr_fun (hσ c) x
  let e := LinearEquiv.ofBijective φ hφ
  have h2 : ∀ c x, e.symm (m (σ c) x) = m c (e.symm x) := fun c x => by
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply, e.symm_apply_eq]
    exact (h1 c x).symm
  constructor
  · intro h f hf y
    let f0 : D →+ F := f.comp e.symm.toLinearMap.toAddMonoidHom
    have hf0 : f0 ∈ letterHom m s τ := by
      refine ⟨fun a x => by simp [f0, hf.1], fun c x => ?_⟩
      obtain ⟨c, rfl⟩ := hσ' c
      simp [f0, h2, hf.2, hτ]
    have := h f0 hf0 (φ y)
    rwa [← hT, show f0 (φ (T y)) = f (T y) from congrArg f (e.symm_apply_apply (T y))] at this
  · intro h f hf y
    obtain ⟨z, rfl⟩ := hφ.2 y
    let f0 : D →+ F := f.comp φ.toAddMonoidHom
    have hf0 : f0 ∈ letterHom m s τ' :=
      ⟨fun a x => by simp [f0, hf.1], fun c x => by simp [f0, h1, hf.2, hτ]⟩
    have := h f0 hf0 z
    rwa [show f0 (T z) = f (φ (T z)) from rfl, hT] at this

theorem commute_aeval_right {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {A B : Module.End R M}
    (h : Commute A B) (p : R[X]) : Commute A (Polynomial.aeval B p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact hp.add_right hr
  | monomial k c =>
    rw [Polynomial.aeval_monomial]
    exact (show Commute (algebraMap R (Module.End R M) c) A from Algebra.commutes c A).symm.mul_right (h.pow_right k)

end General

theorem coe_aeval_of_coe {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    (A : Module.End R p) (f : Module.End R M) (hA : ∀ x : p, ((A x : p) : M) = f x) (q : R[X]) (x : p) :
    ((Polynomial.aeval A q x : p) : M) = Polynomial.aeval f q (x : M) := by
  have hpow : ∀ (n : ℕ) (x : p), (((A ^ n) x : p) : M) = (f ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hA]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow]

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {LL K : FinExt l} {V : Type}
  [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK K) V)

theorem mk_aeval {K F D W : Type} [Field K] [Field F] [AddCommGroup D] [Module K D] [AddCommGroup W] [Module F W]
    (φ : K →+* F) (mk : D →+ W) (hmk : ∀ a x, mk (a • x) = φ a • mk x) (A : Module.End K D)
    (R : Module.End F W) (hR : ∀ y, R (mk y) = mk (A y)) (q : K[X]) (x : D) :
    Polynomial.aeval R (q.map φ) (mk x) = mk (Polynomial.aeval A q x) := by
  have hpow : ∀ (n : ℕ) (x : D), (R ^ n) (mk x) = mk ((A ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hR, ih]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq,
      map_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hpow, hmk]

end Local

section Local2
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {LL K : FinExt l} {V : Type}
  [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK K) V)

set_option maxHeartbeats 2000000 in

theorem letterHom_eq_zero (f : ↥(Dpst P ρ) →+ Om l)
    (hf : f ∈ letterHom (mulD P ρ) ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
      (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))) (y : ↥(Dpst P ρ)) (hy : wdMk P ι ρ y = 0) : f y = 0 := by
  have hfm : ∀ (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)), f (mulD P ρ c x) = algebraMap ↥(MaximalUnramifiedExtension l) (Om l) c * f x := hf.2
  letI := algC ι LL
  obtain ⟨f2, hf2⟩ : ∃ f2 : ℂ ⊗[↥LL.1] ↥(Dpst P ρ) →ₗ[ℂ] ℂ, ∀ (a : ℂ) (x : ↥(Dpst P ρ)),
      f2 (a ⊗ₜ x) = a * ι (f x) := by
    let f1 : ↥(Dpst P ρ) →ₗ[↥LL.1] ℂ :=
      { toFun := fun x => ι (f x), map_add' := fun x y => by rw [map_add, map_add]
        map_smul' := fun a x => by
          rw [hf.1, map_mul, RingHom.id_apply, Algebra.smul_def]; rfl }
    exact ⟨LinearMap.liftBaseChange ℂ f1, fun a x => by simp [f1, LinearMap.liftBaseChange_tmul]⟩
  have h2 : letterKer (mulD P ρ) ℂ (urC ι) ≤ LinearMap.ker f2 := by
    refine iSup_le fun c => ?_
    rw [LinearMap.range_le_ker_iff]
    refine AlgebraTensorModule.ext fun a x => ?_
    have e1 : (f2 ∘ₗ (LinearMap.baseChange ℂ ((mulD P ρ) c) - (urC ι) c • LinearMap.id)) (a ⊗ₜ[↥LL.1] x) =
        f2 (a ⊗ₜ[↥LL.1] (mulD P ρ c x)) - urC ι c * f2 (a ⊗ₜ[↥LL.1] x) := by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
    have e2 : ι (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) c) = urC ι c := rfl
    have e3 : f2 (a ⊗ₜ[↥LL.1] (mulD P ρ c x)) = a * (ι (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) c) * ι (f x)) := by
      rw [hf2, hfm, map_mul]
    have e4 := hf2 a x
    rw [e1, LinearMap.zero_apply]
    linear_combination e3 - urC ι c * e4 + a * ι (f x) * e2
  have hmem : (1 : ℂ) ⊗ₜ[↥LL.1] y ∈ letterKer (mulD P ρ) ℂ (urC ι) := by
    have h0 : letterQ (mulD P ρ) ℂ (urC ι) ((1 : ℂ) ⊗ₜ[↥LL.1] y) = 0 := hy
    rwa [← LinearMap.mem_ker, ker_letterQ] at h0
  have h3 := h2 hmem
  rw [LinearMap.mem_ker, hf2, one_mul] at h3
  exact (map_eq_zero_iff ι ι.injective).mp h3
end Local2

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
open Classical in

theorem aeval_stRep_eq_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V), GlobalTheory.Pst.IsPst P ρ → ∀ (σ : ↥(Ine (F := E) A)) (q : (↥LL.1)[X]), q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = (GlobalTheory.Pst.wdPst P ι Bw h hj ρ).charPol (GlobalTheory.WeilDeligne.ineIncl h σ) → ∀ x ∈ GlobalTheory.Pst.Dpst P ρ, Polynomial.aeval (GlobalTheory.Pst.stRep P ρ (GlobalTheory.Pst.weilToGK Bw h (GlobalTheory.WeilDeligne.ineIncl h σ))) q x = 0 := by
  intro l _ P AI _ ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ hV σ q hq x hx
  haveI hfin := hV.finite
  haveI := LL.2
  set g := weilToGK Bw h (ineIncl h σ) with hg
  set T : Module.End ↥LL.1 ↥(Dpst P ρ) := Polynomial.aeval (actD P ρ g) q with hTdef

  have hR : ∀ y, wdRho P ι Bw h hj ρ (ineIncl h σ) (wdMk P ι ρ y) = wdMk P ι ρ (actD P ρ g y) := fun y => by
    rw [wdRho_mk, weilD_ineIncl]
  have hlet : ∀ y, wdMk P ι ρ (T y) = 0 := fun y => by
    have := mk_aeval (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l)))
      (AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)) (fun a x => wdMk_smul P ι ρ a x)
      (actD P ρ g) (wdRho P ι Bw h hj ρ (ineIncl h σ)) hR q y
    rw [hq, GlobalTheory.Pst.DpstMap.charPol_wdPst P ι Bw h hj ρ hV,
      LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at this
    exact this.symm

  have hφc : Commute (phiD P ρ) T := commute_aeval_right (phiD_actD P ρ g) q
  have hφT : ∀ y, phiD P ρ (T y) = T (phiD P ρ y) := fun y => LinearMap.congr_fun hφc.eq y

  let d : (↥LL.1 →ₐ[ℚ_[l]] Om l) → ℕ := fun s =>
    if Kills (mulD P ρ) (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) T then 1 else 0
  have hd : ∀ s t, d s = d t := GlobalTheory.Pst.LetterDim.const_of_invariant d
    (fun g' hg' s => by
      have key := kills_comp_iff (mulD P ρ) g'.toRingEquiv (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
        (((g' : Om l →ₐ[ℚ_[l]] Om l).comp s : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
        (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) (fun _ => rfl) (fun c => hg' c) T
      simp only [d, key])
    (fun g' hg' s => by
      have key1 := kills_comp_iff (mulD P ρ) g'.toRingEquiv (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
        (((g' : Om l →ₐ[ℚ_[l]] Om l).comp s : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
        ((algebraMap ↥(MaximalUnramifiedExtension l) (Om l)).comp (frobUr l : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l))) (fun _ => rfl) (fun c => hg' c) T
      have key2 := kills_frob (mulD P ρ) (phiD P ρ) phiD_bijective (frobUr l) (phiD_mulD P ρ)
        frobUr_bijective.2 (((g' : Om l →ₐ[ℚ_[l]] Om l).comp s : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
        (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) ((algebraMap ↥(MaximalUnramifiedExtension l) (Om l)).comp (frobUr l : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l)))
        (fun _ => rfl) T hφT
      simp only [d, key1, key2])
  have h0 : Kills (mulD P ρ) ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
      (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) T :=
    fun f hf y => letterHom_eq_zero P ι ρ f hf (T y) (hlet y)
  have hall : ∀ s : ↥LL.1 →ₐ[ℚ_[l]] Om l, Kills (mulD P ρ) (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) T := by
    intro s
    have e := hd s LL.1.val
    have e1 : d LL.1.val = 1 := if_pos h0
    rw [e1] at e
    by_contra hs
    have : d s = 0 := if_neg hs
    omega

  have hT0 : T ⟨x, hx⟩ = 0 := by
    letI : Module ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := inferInstanceAs (Module ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))
    haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := hfin
    refine GlobalTheory.T.eq_zero_of_forall_letterType_functional (k := ℚ_[l]) (F := Om l) (mulD P ρ) (fun _ _ => rfl) (fun c x => Subtype.ext (by
      have : mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = algebraMap ℚ_[l] ↥LL.1 c • LinearMap.id :=
        end_ext P fun v b => by
          rw [mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul,
            LinearMap.smul_apply, algebraMap_smul, LinearMap.id_apply]
      rw [coe_mulD, this]
      rfl)) (T ⟨x, hx⟩) fun s f hf => hall s f hf ⟨x, hx⟩
  have := coe_aeval_of_coe (p := Dpst P ρ) (actD P ρ g) (stRep P ρ g) (fun _ => rfl) q ⟨x, hx⟩
  rw [← this]
  exact congrArg Subtype.val hT0

end GlobalTheory.IneKillsDpst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalKillsPotCrystallineOfKillsPotSemistable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

open TensorProduct GlobalTheory.Pst GlobalTheory.PstLine

namespace GlobalTheory.PcrisPst

theorem fixed_of_mem_Dpcris {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L : FinExt l) (h : K.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    (ρ : Representation ↥L.1 ↥(GK K) V) {d : V ⊗[ℚ_[l]] P.R.B} (hd : d ∈ (pc P h hN hF hS).Dpcris ρ)
    (x : ↥(GKin h)) : actVB (P.PD K) ρ (x : ↥(GK K)) d = d := by
  simp only [Formalism.WeaklyAdmissibleFiltrations.PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hd
  have := hd x
  have e : actVB (pc P h hN hF hS).PD' ((pc P h hN hF hS).resH ρ) x = actVB (P.PD K) ρ (x : ↥(GK K)) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    have := (pc P h hN hF hS).actB_eq x b
    simp [actVB, Formalism.WeaklyAdmissibleFiltrations.PotCrysData.resH] at this ⊢
    rw [this]
    rfl
  rw [← e]; exact this

section Map

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

theorem stMap_crisIncl_pow (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (n : ℕ)
    (x : V ⊗[ℚ_[l]] P.R.B) :
    stMap P f (crisIncl P ↥L.1 V ((actVB (P.PD K) ρ g ^ n) x)) =
      (stRep P ρ' g ^ n) (stMap P f (crisIncl P ↥L.1 V x)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← stRep_crisIncl,
      stMap_stRep P he, ih]

theorem stMap_crisIncl_aeval {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ') (g : ↥(GK K)) (q : (↥L.1)[X])
    (x : V ⊗[ℚ_[l]] P.R.B) :
    stMap P f (crisIncl P ↥L.1 V (Polynomial.aeval (actVB (P.PD K) ρ g) q x)) =
      Polynomial.aeval (stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom)
        (stMap P f (crisIncl P ↥L.1 V x)) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hr]
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, stMap_smul P f (hm.smul a),
      stMap_crisIncl_pow P hm.equiv]
    rfl

end Map

theorem aeval_eq_zero_of_kills_Dpst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L L' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (hL : L.1 ≤ L'.1) {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V'] (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V') (f : V →ₗ[ℚ_[l]] V'), Function.Injective f → GlobalTheory.PstLine.IsMor hL f ρ ρ' → ∀ (g : ↥(GK K)) (q : (↥L.1)[X]), (∀ y ∈ GlobalTheory.Pst.Dpst P ρ', Polynomial.aeval (GlobalTheory.Pst.stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom) y = 0) → ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, Polynomial.aeval (actVB (P.PD K) ρ g) q d = 0 := by
  intro l _ P K K' L L' h hN hF hS hL V V' _ _ _ _ _ _ _ _ ρ ρ' f hf hm g q hq d hd
  have hmem : crisIncl P ↥L.1 V d ∈ Dpst P ρ :=
    (mem_Dpst P ρ).2 ⟨K', fun g' hg' => by
      rw [stRep_crisIncl, fixed_of_mem_Dpcris P K K' L h hN hF hS ρ hd ⟨g', hg'⟩]⟩
  have hinj : Function.Injective (stMap P f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  apply crisIncl_injective P (LL := ↥L.1) (V := V)
  apply hinj
  rw [stMap_crisIncl_aeval P hm g q d, map_zero, map_zero]
  exact hq _ (stMap_mem_Dpst P hm.equiv hmem)

end GlobalTheory.PcrisPst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPolyInertiaOfPotSemistableEnlargement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.PstModel

theorem charPol_upRep_of_isPstAt : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∃ (LL' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ LL'.1), GlobalTheory.Pst.IsPst (D.loc (D.nd.l i)) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))))) ∧ ∀ (σ : Gw D.nd w) (hσ : (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (p : (D.nd.O i)[X]), p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ((p.map (D.nbr i w hw).toLL).map (IntermediateField.inclusion hL).toRingHom).map ((D.naut.iotaQC i).toRingHom.comp (algebraMap ↥LL'.1 (Om (D.nd.l i)))) = (GlobalTheory.Pst.wdPst (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w)))))).charPol (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) := by
  intro D i w hw m r h
  obtain ⟨LL', r', ⟨hL, hmod⟩, hpst, hwd⟩ := GlobalTheory.Pst.wdAt_of_isPstAt (P := D.loc (D.nd.l i)) (D.naut.iotaQC i)
    (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) h
  have key : r' = GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))) := by
    ext g a b
    have h1 := congrArg (fun f => ((f g : GL (Fin m) (Om (D.nd.l i))) : Matrix (Fin m) (Fin m) (Om (D.nd.l i))) a b) hmod
    have h2 := (D.loc_tie i w hw).1 (((r g : GL (Fin m) (D.nd.O i)) : Matrix (Fin m) (Fin m) (D.nd.O i)) a b)
    simp only [mapRep, GlobalTheory.Pst.resDec, GlobalTheory.PstLine.upRep] at h1 ⊢
    simp at h1 ⊢
    exact h1.trans h2
  refine ⟨LL', hL, key ▸ hpst, ?_⟩
  intro σ hσ p hp
  rw [← key, ← hwd, ← GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine, ← hp, Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext x
  have h2 := (D.loc_tie i w hw).1 x
  simp only [iotaO, iotaOQ] at h2 ⊢
  simp at h2 ⊢
  exact h2.symm

end GlobalTheory.PstModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_principalLevel_eq_const_mul_classSum : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  first | exact @GlobalTheory.ClassSumPrinc.classSum_princ_eq | exact GlobalTheory.ClassSumPrinc.classSum_princ_eq | (intros; apply GlobalTheory.ClassSumPrinc.classSum_princ_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateCompletionIso
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjDualParam

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (κ : w.adicCompletion D.host.E ≃+* w'.adicCompletion D.host.E), Continuous κ →
    (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)))
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w'.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
    (∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a)) →
    ∃ (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
      GlobalTheory.WeilDeligne.WD.mk b = (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)).lpDual ∧
      GlobalTheory.WeilDeligne.WD.mk b' = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w') (GlobalTheory.LocLanglands.cls σ') ∧
      b.N = b'.N ∧ ∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ' := by
  intro hP hL D w w' c hc hA κ hκ hκE n σ σ' e he
  let π₁ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose n),
      fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose n),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose n g⟩) σ.irr⟩
  have ha : GlobalTheory.PRep.IsAdmissible σ.ρ := (hP.bz _).1 (Fin n) σ.V σ.ρ σ.smooth σ.irr
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irr
  have hr := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)
  obtain ⟨b, b', h1, h2, h3, h4⟩ := hL.2 _ _ _ _ _ _ _ _ _ _ _ _ hr
    (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w')) c (D.host.conj : D.host.E →+* D.host.E) κ
    (fun z => (hA z).symm) hc hκ hκE n π₁ σ' e he
  obtain ⟨_, _, _, -, H⟩ := hr
  exact ⟨b, b', h1.trans (H.dual n σ π₁ hE), h2, h3, h4⟩

end GlobalTheory.ConjDualParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsMulStableWeberValuesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat
open GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverSections_mul_stable_weberValues : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l : Level Q.H) (Xo : Moduli (Q.Dw j) l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK (Q.Dw j) V io → 1 ≤ (Q.Dw j).p + (Q.Dw j).q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → ∀ N : ℕ, 0 < N → l.M' ∣ N → (WeberIn Q.H c.F N ∨ CurveOver Q.H c.F N) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  first | exact @GlobalTheory.CompMul.sec_mul_of_weberIn | exact GlobalTheory.CompMul.sec_mul_of_weberIn | (intros; apply GlobalTheory.CompMul.sec_mul_of_weberIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVectorStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  first | exact @GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | exact GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | (intros; apply GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR <;> assumption)
end

