import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0260
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem pushforward_map_smulHom_appTop (φ : Z ⟶ X) (H : Z.Modules) (r : Γ(X, ⊤)) :
    (Scheme.Modules.pushforward φ).map (GroundTheory.Arith.SchemeCoh.smulHom H (φ.appTop r)) =
      GroundTheory.Arith.SchemeCoh.smulHom ((Scheme.Modules.pushforward φ).obj H) r := by
  ext U x
  rw [GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.QCoh.pushforward_smul]
  refine (GroundTheory.Arith.SchemeCoh.smulHom_app_apply H (φ.appTop r) (φ ⁻¹ᵁ U) x).trans ?_
  congr 1
  unfold GroundTheory.Arith.SchemeCoh.restrictTop
  have h := φ.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g r) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2.symm

theorem pullback_map_smulHom_appTop (φ : Z ⟶ X) (E : X.Modules) (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullback φ).map (GroundTheory.Arith.SchemeCoh.smulHom E a) =
      GroundTheory.Arith.SchemeCoh.smulHom _ (φ.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom_appTop]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality _).symm.trans
    (GroundTheory.Arith.SchemeCoh.smulHom_comp _ _)

theorem pullback_map_comp_eq_zero_iff (φ : Z ⟶ X) {D E : X.Modules} {Q : Z.Modules} (f : D ⟶ E)
    (q : (Scheme.Modules.pullback φ).obj E ⟶ Q) :
    (Scheme.Modules.pullback φ).map f ≫ q = 0 ↔
      f ≫ (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E Q q = 0 := by
  rw [← Adjunction.homEquiv_naturality_left]
  constructor
  · intro h
    rw [h, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
  · intro h
    apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv D Q).injective
    rw [h, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

theorem appTop_algebraMap [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (a : A) :
    φ.appTop (algebraMap A Γ(X, ⊤) a) = algebraMap A Γ(Z, ⊤) a := by
  unfold GroundTheory.Arith.SchemeCoh.algebraOfOver GroundTheory.Arith.SchemeCoh.overAlgebra
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  rw [← hφ, Scheme.Hom.comp_appTop]
  rfl

theorem exists_smulHom_eq_comp_idealSumMap [X.Over (Spec (.of A))] (F : X.Modules) (J : Ideal A) {a : A}
    (ha : a ∈ J) : ∃ L : F ⟶ (⨁ fun _ : Fin (idealGenNum J) => F),
      GroundTheory.Arith.SchemeCoh.smulHom F (algebraMap A Γ(X, ⊤) a) = L ≫ idealSumMap F J := by
  rw [← GroundTheory.Arith.SchemeCoh.span_idealGen J] at ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  refine ⟨biproduct.lift fun k => GroundTheory.Arith.SchemeCoh.smulHom F (algebraMap A Γ(X, ⊤) (c k)), ?_⟩
  rw [GroundTheory.Arith.SchemeCoh.idealSumMap, biproduct.lift_desc, ← hc, map_sum,
    GroundTheory.Arith.SchemeCoh.smulHom_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, map_mul, GroundTheory.Arith.SchemeCoh.smulHom_comp_smulHom]

theorem arrow_comp_cokernel_eq_zero {C : X.Modules} {D T : Subobject C} (h : D ≤ T) :
    D.arrow ≫ cokernel.π T.arrow = 0 := by
  rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, Limits.comp_zero]

theorem pullback_idealPowι_comp_eq_zero [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (n : ℕ)
    {T : Subobject ((Scheme.Modules.pullback φ).obj E)}
    (hT : powSub I ((Scheme.Modules.pullback φ).obj E) n ≤ T) :
    (Scheme.Modules.pullback φ).map (idealPowι I E n) ≫ cokernel.π T.arrow = 0 := by
  have h0 : kernel.ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap
      ((Scheme.Modules.pullback φ).obj E) (I ^ n))) ≫ cokernel.π T.arrow = 0 := by
    change GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E) n ≫
      cokernel.π T.arrow = 0
    have e := Subobject.underlyingIso_arrow
      (GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E) n)
    have e2 : (Subobject.mk (GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E)
        n)).arrow ≫ cokernel.π T.arrow = 0 := arrow_comp_cokernel_eq_zero hT
    rw [← e, Category.assoc, e2, Limits.comp_zero]
  have hz : GroundTheory.Arith.SchemeCoh.idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ n) ≫
      cokernel.π T.arrow = 0 := by
    rw [← kernel.lift_ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap _ (I ^ n)))
      (GroundTheory.Arith.SchemeCoh.idealSumMap _ (I ^ n)) (cokernel.condition _), Category.assoc, h0,
      Limits.comp_zero]
  have key : GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _ (cokernel.π T.arrow) = 0 := by
    rw [GroundTheory.Arith.SchemeCoh.idealSumMap]
    apply biproduct.hom_ext'
    intro k
    rw [biproduct.ι_desc_assoc, Limits.comp_zero, ← Adjunction.homEquiv_naturality_left,
      pullback_map_smulHom_appTop, appTop_algebraMap φ hφ]
    obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ n)
      (GroundTheory.Arith.SchemeCoh.idealGen_mem (I ^ n) k)
    rw [hL, Category.assoc, hz, Limits.comp_zero, Adjunction.homEquiv_unit, Functor.map_zero,
      Limits.comp_zero]
  rw [pullback_map_comp_eq_zero_iff]
  rw [show GroundTheory.Arith.SchemeCoh.idealPowι I E n =
      kernel.ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n))) from rfl,
    ← cokernel.π_desc (GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n)) _ key, kernel.condition_assoc,
    Limits.zero_comp]

private theorem isQuasicoherent_imageSubobject_of_isQuasicoherent {W : Scheme.{0}} {M N : W.Modules} (f : M ⟶ N)
    (T : Subobject N) (hT : T = imageSubobject f) :
    SheafOfModules.IsQuasicoherent M ∧ SheafOfModules.IsQuasicoherent N →
      SheafOfModules.IsQuasicoherent (Subobject.underlying.obj T) := by
  subst hT
  have e := (imageSubobjectIso f).symm
  intro h
  exact @GlobalTheory.QCoh.isQuasicoherent_of_iso _ _ _ e (@GlobalTheory.QCoh.isQuasicoherent_image _ _ _ f h.1 h.2)

theorem closedSys_pullSys {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))]
    [IsLocallyNoetherian X] (φ : Z ⟶ X) (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    {E : X.Modules} (hE : IsCoherent E) {S : ℕ → Subobject E} (hS : ClosedSys I E S) :
    ClosedSys I ((Scheme.Modules.pullback φ).obj E) (pullSys I φ E S) := by
  have hle : ∀ e, S (e + 1) ≤ S e := fun e => by
    rw [hS.succ e]
    exact le_sup_left
  unfold GlobalTheory.CompanionTheory.GE.pullSys
  refine ⟨fun e => ?_, fun e => le_sup_right, fun e => ?_⟩
  · have hpb : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pullback φ).obj E) :=
      @GlobalTheory.QCoh.isQuasicoherent_pullback _ _ φ E hE.1
    exact (GlobalTheory.CompanionTheory.GE.supsecs hpb _ _
      (isQuasicoherent_imageSubobject_of_isQuasicoherent ((Scheme.Modules.pullback φ).map (S e).arrow) _ rfl
        ⟨@GlobalTheory.QCoh.isQuasicoherent_pullback _ _ φ _ (hS.qcoh e), hpb⟩)
      ((@closedSys_pow A _ _ I _ _ ((Scheme.Modules.pullback φ).obj E) hpb).qcoh e)).1
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      generalize hT : (imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ⊔
          powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1 + 1)) ⊔
          powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1) = T
      have hT1 : imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ≤ T := by
        rw [← hT]
        exact le_sup_left.trans le_sup_left
      have hT2 : powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1) ≤ T := by
        rw [← hT]
        exact le_sup_right
      have hK : S e ≤ kernelSubobject ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _
          (cokernel.π T.arrow)) := by
        rw [hS.succ e]
        refine sup_le (le_kernelSubobject _ _ ?_) (le_kernelSubobject _ _ ?_)
        · refine (pullback_map_comp_eq_zero_iff φ _ _).1 ?_
          have e1 := imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow)
          refine (congrArg (· ≫ cokernel.π T.arrow) e1).symm.trans ?_
          rw [Category.assoc, arrow_comp_cokernel_eq_zero hT1, Limits.comp_zero]
        · have e2 := (pullback_map_comp_eq_zero_iff φ _ _).1
            (pullback_idealPowι_comp_eq_zero I φ hφ E (e + 1) hT2)
          have e3 := Subobject.underlyingIso_hom_comp_eq_mk
            (GroundTheory.Arith.SchemeCoh.idealPowι I E (e + 1))
          exact (congrArg (· ≫ _) e3.symm).trans
            ((Category.assoc _ _ _).trans (by rw [e2]; exact Limits.comp_zero))
      have hz : (S e).arrow ≫ (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _
          (cokernel.π T.arrow) = 0 := by
        rw [← Subobject.ofLE_arrow hK, Category.assoc, kernelSubobject_arrow_comp, Limits.comp_zero]
      exact imageSubobject_le _ (Abelian.monoLift _ _ ((pullback_map_comp_eq_zero_iff φ _ _).2 hz))
        (Abelian.monoLift_comp _ _ _)
    · have him : imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ≤
          imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) := by
        rw [← Subobject.ofLE_arrow (hle e), Functor.map_comp]
        exact imageSubobject_comp_le _ _
      exact sup_le (sup_le (him.trans le_sup_left)
        ((powSub_succ_le I _ (e + 1)).trans le_sup_right)) le_sup_right

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureConjugationInvariant
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.MemConj

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem denseRange_algebraMap_Kp (u : Pl F) : DenseRange (algebraMap F (Kp u)) := by
  cases u with
  | inl w =>
    exact (Function.surjective_eval w).denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F)
      (continuous_apply w)
  | inr v => exact HeightOneSpectrum.denseRange_algebraMap (K := F) v

def qinv {K : Type} [Field K] [Algebra F K] (e : Q d β K) : Q d β K :=
  algebraMap K (Q d β K) (qn e)⁻¹ * star e

theorem mul_qinv {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    e * qinv e = 1 := by
  have h1 : e * algebraMap K (Q d β K) (qn e)⁻¹ = algebraMap K (Q d β K) (qn e)⁻¹ * e :=
    (Algebra.commutes _ _).symm
  rw [qinv, ← mul_assoc, h1, mul_assoc, mul_star_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem qinv_mul {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    qinv e * e = 1 := by
  rw [qinv, mul_assoc, star_mul_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem qinv_unique {K : Type} [Field K] [Algebra F K] {e e' : Q d β K} (h : qn e ≠ 0)
    (h' : e' * e = 1) : qinv e = e' := by
  calc qinv e = (e' * e) * qinv e := by rw [h', one_mul]
    _ = e' := by rw [mul_assoc, mul_qinv h, mul_one]

theorem conj_mem_SuppAt {T : Set (Pl F)} {p q h : Q d β (AF F)} (hpq : p * q = 1)
    (hh : h ∈ SuppAt d β T) : p * h * q ∈ SuppAt d β T := by
  refine ⟨?_, fun u hu => ?_⟩
  · rw [qn_mul, qn_mul, hh.1, mul_one, ← qn_mul, hpq, qn_one]
  · rw [map_mul, map_mul, hh.2 u hu, mul_one, ← map_mul, hpq, map_one]

theorem conj_mem_SAQ (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ SAQ d β s) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ SAQ d β s := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hx
  have r1 : (rat δ : Q d β (AF F)) * rat δ' = 1 := by rw [← map_mul, h1, map_one]
  have r2 : (rat δ' : Q d β (AF F)) * rat δ = 1 := by rw [← map_mul, h2, map_one]
  refine ⟨δ * γ * δ', ?_, rat δ * h * rat δ', conj_mem_SuppAt r1 hh, ?_⟩
  · rw [qn_mul, qn_mul, hγ, mul_one, ← qn_mul, h1, qn_one]
  · rw [map_mul, map_mul]
    calc (rat δ : Q d β (AF F)) * (rat γ * h) * rat δ'
        = rat δ * rat γ * (rat δ' * rat δ) * h * rat δ' := by
          rw [r2, mul_one]; simp only [mul_assoc]
      _ = rat δ * rat γ * rat δ' * (rat δ * h * rat δ') := by simp only [mul_assoc]

theorem conj_mem_closure (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ closure (SAQ d β s)) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ closure (SAQ d β s) := by
  have hc : Continuous fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ' :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hsub : closure (SAQ d β s) ⊆
      (fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ') ⁻¹' closure (SAQ d β s) := by
    refine closure_minimal (fun y hy => subset_closure ?_) (isClosed_closure.preimage hc)
    exact conj_mem_SAQ s h1 h2 hy
  exact hsub hx

def psi (w : Pl F) (y : Q d β (Kp w)) : Q d β (AF F) :=
  ⟨1 + inc w (y.re - 1), inc w y.imI, inc w y.imJ, inc w y.imK⟩

theorem continuous_psi (w : Pl F) : Continuous (psi (d := d) (β := β) w) := by
  rw [continuous_q_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))
  · exact (continuous_inc w).comp continuous_imI
  · exact (continuous_inc w).comp continuous_imJ
  · exact (continuous_inc w).comp continuous_imK

theorem psi_proj {w : Pl F} {x : Q d β (AF F)} (hx : x ∈ SuppAt d β {w}) :
    psi w (qmap (proj w) x) = x := by
  have key : ∀ u, u ≠ w → qmap (proj u) x = 1 := fun u hu => hx.2 u (by simpa using hu)
  ext
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.re) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imI) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imJ) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imK) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm

theorem qmap_proj_rat (w : Pl F) (δ : Q d β F) :
    qmap (proj w) (rat δ : Q d β (AF F)) = rat δ := by
  ext <;> simp [rat, qmap]

theorem continuous_qn {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (qn : Q d β K → K) := by
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  unfold qn
  fun_prop

theorem continuous_star_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (star : Q d β K → Q d β K) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  exact ⟨h1.add (continuous_const.mul h2), h2.neg, h3.neg, h4.neg⟩

theorem continuous_algebraMap_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (algebraMap K (Q d β K)) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.algebraMap_eq]
  exact ⟨continuous_id, continuous_const, continuous_const, continuous_const⟩

theorem continuousAt_qinv {K : Type} [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] {e : Q d β K} (h : qn e ≠ 0) : ContinuousAt qinv e := by
  have h1 : ContinuousAt (fun x : Q d β K => (qn x)⁻¹) e :=
    continuous_qn.continuousAt.inv₀ h
  have h2 : ContinuousAt (fun x : Q d β K => algebraMap K (Q d β K) (qn x)⁻¹) e :=
    continuous_algebraMap_q.continuousAt.comp h1
  exact h2.mul continuous_star_q.continuousAt

theorem denseRange_rat (w : Pl F) : DenseRange (rat : Q d β F → Q d β (Kp w)) := by
  have D := denseRange_algebraMap_Kp (F := F) w
  have h := D.prodMap (D.prodMap (D.prodMap D))
  have h2 := ((qHomeo (d := d) (β := β) (R := Kp w)).symm.surjective.denseRange).comp h
    (qHomeo (d := d) (β := β) (R := Kp w)).symm.continuous
  refine Dense.mono ?_ h2
  rintro _ ⟨⟨a, b, c, e⟩, rfl⟩
  exact ⟨⟨a, b, c, e⟩, rfl⟩

theorem mem_closure_of_conj_mem : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
    ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
      ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
      a ∈ closure (SAQ d β s) := by
  intro F _ _ d β _ s w a ha c hc
  have ha' : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ SuppAt d β {w} :=
    conj_mem_SuppAt c.inv_mul ha
  obtain ⟨a', ea'⟩ : ∃ a' : Q d β (AF F),
      a' = ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) := ⟨_, rfl⟩
  rw [← ea'] at ha' hc
  obtain ⟨y, ey⟩ : ∃ y : Q d β (Kp w), y = qmap (proj w) a' := ⟨_, rfl⟩
  obtain ⟨cw, ecw⟩ : ∃ cw : Q d β (Kp w), cw = qmap (proj w) (c : Q d β (AF F)) := ⟨_, rfl⟩
  obtain ⟨cw', ecw'⟩ : ∃ cw' : Q d β (Kp w),
      cw' = qmap (proj w) ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) := ⟨_, rfl⟩
  have h1 : cw * cw' = 1 := by rw [ecw, ecw', ← map_mul, c.mul_inv, map_one]
  have h2 : cw' * cw = 1 := by rw [ecw, ecw', ← map_mul, c.inv_mul, map_one]
  have hq : qn cw ≠ 0 := by
    intro h0
    have := congrArg qn h1
    rw [qn_mul, h0, zero_mul, qn_one] at this
    exact zero_ne_one this
  have hinv : qinv cw = cw' := qinv_unique hq h2
  have hy : y = cw' * qmap (proj w) a * cw := by rw [ey, ea', map_mul, map_mul, ecw, ecw']
  have hga : psi w (cw * y * qinv cw) = a := by
    have : cw * y * qinv cw = qmap (proj w) a := by
      rw [hinv, hy]
      calc cw * (cw' * qmap (proj w) a * cw) * cw'
          = (cw * cw') * qmap (proj w) a * (cw * cw') := by simp only [mul_assoc]
        _ = qmap (proj w) a := by rw [h1, one_mul, mul_one]
    rw [this, psi_proj ha]
  have hcont : ContinuousAt (fun e : Q d β (Kp w) => psi w (e * y * qinv e)) cw :=
    (continuous_psi w).continuousAt.comp
      ((continuousAt_id.mul continuousAt_const).mul (continuousAt_qinv hq))
  have hcl : cw ∈ closure (Set.range (rat : Q d β F → Q d β (Kp w))) := denseRange_rat w cw
  haveI : (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hcl
  have htend : Filter.Tendsto (fun e : Q d β (Kp w) => psi w (e * y * qinv e))
      (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw) (𝓝 a) := by
    have := hcont.tendsto
    rw [hga] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hopen : IsOpen {e : Q d β (Kp w) | qn e ≠ 0} :=
    isOpen_ne.preimage continuous_qn
  rw [← closure_closure]
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds hq)] with e he he0
  obtain ⟨δ, rfl⟩ := he
  have hδ : qn δ ≠ 0 := by
    intro h0
    apply he0
    rw [rat, qn_qmap, h0, map_zero]
  have i1 : δ * qinv δ = 1 := mul_qinv hδ
  have i2 : qinv δ * δ = 1 := qinv_mul hδ
  have r1 : (rat δ : Q d β (AF F)) * rat (qinv δ) = 1 := by rw [← map_mul, i1, map_one]
  have hmem := conj_mem_closure s i1 i2 hc
  have hsupp := conj_mem_SuppAt r1 ha'
  have hw : (qinv (rat δ : Q d β (Kp w))) = rat (qinv δ) :=
    qinv_unique he0 (by rw [← map_mul, i2, map_one])
  have : psi w ((rat δ : Q d β (Kp w)) * y * qinv (rat δ : Q d β (Kp w))) =
      (rat δ : Q d β (AF F)) * a' * rat (qinv δ) := by
    rw [hw, ey, ← qmap_proj_rat w δ, ← qmap_proj_rat w (qinv δ), ← map_mul, ← map_mul]
    exact psi_proj hsupp
  rw [this]
  exact hmem

end GlobalTheory.CompanionTheory.PlaneSA.MemConj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmExtensionImaginaryGenerator
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem cm_exists_sqrt_nonsquare : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ d : F, (∀ r : F, r ^ 2 ≠ d) ∧ ∃ ξ : E, ξ ^ 2 = algebraMap F E d ∧ σ ξ = -ξ := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨-, hC, h2, hconj⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)

  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  set τ : E →+* ℂ := w.embedding with hτ

  have hne : ∃ e : E, σ e ≠ e := by
    by_contra hall
    push_neg at hall
    have hreal : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have := hconj τ x
      rw [hall x] at this
      simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex w))
      (InfinitePlace.isReal_iff.mpr hreal)

  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hconj, hconj, star_star]
  obtain ⟨e, he⟩ := hne
  set ξ : E := e - σ e with hξ
  have hξ0 : ξ ≠ 0 := fun h0 => he (sub_eq_zero.mp h0).symm
  have hσξ : σ ξ = -ξ := by
    simp only [hξ, map_sub, hinv, neg_sub]
  have h2E : (2 : E) ≠ 0 := two_ne_zero

  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : algebraMap F E s + algebraMap F E t * ξ = 0 := by
      simpa [Algebra.smul_def] using hst
    have hσ' : algebraMap F E s - algebraMap F E t * ξ = 0 := by
      have := congrArg σ hst'
      simpa [map_add, map_mul, AlgHom.commutes, hσξ, sub_eq_add_neg] using this
    have hs : algebraMap F E s = 0 := by
      have : 2 * algebraMap F E s = 0 := by linear_combination hst' + hσ'
      exact (mul_eq_zero.mp this).resolve_left h2E
    have ht : algebraMap F E t * ξ = 0 := by
      have : 2 * (algebraMap F E t * ξ) = 0 := by linear_combination hst' - hσ'
      exact (mul_eq_zero.mp this).resolve_left h2E
    refine ⟨(map_eq_zero _).mp hs, (map_eq_zero _).mp ((mul_eq_zero.mp ht).resolve_right hξ0)⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  have hmem : ξ ^ 2 ∈ Submodule.span F (Set.range ![(1 : E), ξ]) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
  rw [Fin.sum_univ_two] at hc
  have hc' : algebraMap F E (c 0) + algebraMap F E (c 1) * ξ = ξ ^ 2 := by
    simpa [Algebra.smul_def] using hc
  have hc'' : algebraMap F E (c 0) - algebraMap F E (c 1) * ξ = ξ ^ 2 := by
    have := congrArg σ hc'
    simpa [map_add, map_mul, map_pow, AlgHom.commutes, hσξ, sub_eq_add_neg] using this
  have hb : algebraMap F E (c 1) * ξ = 0 := by
    have : 2 * (algebraMap F E (c 1) * ξ) = 0 := by linear_combination hc' - hc''
    exact (mul_eq_zero.mp this).resolve_left h2E
  have hsq : ξ ^ 2 = algebraMap F E (c 0) := by
    rw [← hc', hb, add_zero]
  refine ⟨c 0, ?_, ξ, hsq, hσξ⟩
  intro r hr
  have hfix : ∀ x : F, σ (algebraMap F E x) = algebraMap F E x := σ.commutes
  have hprod : (ξ - algebraMap F E r) * (ξ + algebraMap F E r) = 0 := by
    have : algebraMap F E (c 0) = algebraMap F E r ^ 2 := by rw [← hr, map_pow]
    linear_combination hsq + this
  have hcontra : ξ = -ξ := by
    rcases mul_eq_zero.mp hprod with h0 | h0
    · have hx : ξ = algebraMap F E r := sub_eq_zero.mp h0
      rw [← hσξ, hx, hfix]
    · have hx : ξ = -algebraMap F E r := eq_neg_of_add_eq_zero_left h0
      rw [← hσξ, hx, map_neg, hfix]
  have : 2 * ξ = 0 := by linear_combination hcontra
  exact hξ0 ((mul_eq_zero.mp this).resolve_left h2E)

end GlobalTheory.CompanionTheory.PlaneSA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_subobject_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (E : X.Modules), E.IsQuasicoherent → ∀ (n : ℕ) (V : X.Opens), IsAffineOpen V → secs (powSub I E n) V = ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_powSub | exact GlobalTheory.CompanionTheory.GE.secs_powSub | (intros; apply GlobalTheory.CompanionTheory.GE.secs_powSub <;> assumption)
end

