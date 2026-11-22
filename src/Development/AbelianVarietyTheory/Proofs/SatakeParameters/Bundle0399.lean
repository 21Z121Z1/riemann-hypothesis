import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0088
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0395
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0382
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0836
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEvalComplexPointLeSpanJacobian
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JacSpan

theorem ker_le_span_sup {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) {d : ℕ} (δ : Fin d → A →+ ℂ)
    (hmul : ∀ b f g, δ b (f * g) = e f * δ b g + e g * δ b f)
    (hc : ∀ b (c : ℂ), δ b (algebraMap ℂ A c) = 0) (g : Fin d → A)
    (hgs : ∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2)
    (φ : Fin d → A) (hdet : (Matrix.of fun a b => δ b (φ a)).det ≠ 0) :
    RingHom.ker e ≤ Ideal.span (Set.range fun j => φ j - algebraMap ℂ A (e (φ j))) ⊔
      RingHom.ker e ^ 2 := by
  classical
  have hsq : ∀ b, ∀ x ∈ RingHom.ker e ^ 2, δ b x = 0 := by
    intro b x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [hmul, RingHom.mem_ker.1 hx, RingHom.mem_ker.1 hy, zero_mul, zero_mul, add_zero]
    · rw [map_add, hx, hy, add_zero]
  have hsmul : ∀ b (c : ℂ) (x : A), δ b (c • x) = c * δ b x := by
    intro b c x
    rw [Algebra.smul_def, hmul, hc, he, mul_zero, add_zero]
  set φ' : Fin d → A := fun j => φ j - algebraMap ℂ A (e (φ j)) with hφ'
  have hφ'e : ∀ j, e (φ' j) = 0 := fun j => by simp only [hφ', map_sub, he, sub_self]
  choose C hC using fun j => hgs (φ' j) (hφ'e j)
  let M : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun k b => δ b (g k)
  have hJ : (Matrix.of fun a b => δ b (φ a)) = Matrix.of C * M := by
    ext a b
    have h1 := hsq b _ (hC a)
    rw [map_sub, map_sum] at h1
    simp only [hsmul] at h1
    have h2 : δ b (φ' a) = δ b (φ a) := by simp only [hφ', map_sub, hc, sub_zero]
    rw [Matrix.of_apply, Matrix.mul_apply, ← h2]
    simp only [M, Matrix.of_apply]
    linear_combination h1
  have hdetC : (Matrix.of C).det ≠ 0 := by
    rw [hJ, Matrix.det_mul] at hdet
    exact left_ne_zero_of_mul hdet
  have hu : IsUnit (Matrix.of C).det := isUnit_iff_ne_zero.2 hdetC
  intro a ha
  obtain ⟨β, hβ⟩ := hgs a (RingHom.mem_ker.1 ha)
  set γ := Matrix.vecMul β (Matrix.of C)⁻¹ with hγdef
  have hγ : Matrix.vecMul γ (Matrix.of C) = β := by
    rw [hγdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hsum : ∑ j, γ j • ∑ k, C j k • g k = ∑ k, β k • g k := by
    rw [← hγ]
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul,
      Matrix.of_apply]
    exact Finset.sum_comm
  have hspan : ∑ j, γ j • φ' j ∈ Ideal.span (Set.range φ') :=
    Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hrest : a - ∑ j, γ j • φ' j ∈ RingHom.ker e ^ 2 := by
    have h3 : a - ∑ j, γ j • φ' j =
        (a - ∑ k, β k • g k) - ∑ j, γ j • (φ' j - ∑ k, C j k • g k) := by
      rw [← hsum]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [h3]
    exact sub_mem hβ (Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hC j))
  have h4 : a = (a - ∑ j, γ j • φ' j) + ∑ j, γ j • φ' j := by abel
  rw [h4]
  exact add_mem (Ideal.mem_sup_right hrest) (Ideal.mem_sup_left hspan)

end GlobalTheory.JacSpan

open GlobalTheory.ChartGlue in

theorem GlobalTheory.JacSpan.ker_le_span_jac : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  intro X p d _ U hU ch φ z hzc hz hdet
  obtain ⟨g, _, hgs, _⟩ := GlobalTheory.CotDim.exists_cotangent_basis X p d U hU z hz
  have hd : ∀ f : Γ(X, U), DifferentiableAt ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) :=
    fun f => ch.differentiableAt_ev f hzc hz
  have hn : ∀ᶠ v in nhds (ch.e z), ch.e.symm v ∈ CxPts.ptsIn p (RingHom.id ℂ) U :=
    Filter.eventually_of_mem ((isOpen_over ch.e (CxPts.isOpen_ptsIn U)).mem_nhds
      (mem_over ch.e hzc hz)) fun _ h => h.2
  let δ : Fin d → Γ(X, U) →+ ℂ := fun b => AddMonoidHom.mk' (fun f =>
      fderiv ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) (EuclideanSpace.single b 1))
    (fun f g => by
      have e : CxPts.ev p (RingHom.id ℂ) U (f + g) ∘ ch.e.symm =
          (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) + (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
        funext fun v => CxPts.ev_add _ _ _
      simp only [e, fderiv_add (hd f) (hd g), ContinuousLinearMap.add_apply])
  have hmul : ∀ b (f g : Γ(X, U)), δ b (f * g) =
      CxPts.evHom hz f * δ b g + CxPts.evHom hz g * δ b f := by
    intro b f g
    have e : CxPts.ev p (RingHom.id ℂ) U (f * g) ∘ ch.e.symm =
        (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) * (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
      funext fun v => CxPts.ev_mul _ _ _
    simp only [δ, AddMonoidHom.mk'_apply, e, fderiv_mul (hd f) (hd g), Function.comp_apply,
      ch.e.left_inv hzc, CxPts.ev_eq hz, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc : ∀ b (c : ℂ), δ b (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) = 0 := by
    intro b c
    have e : CxPts.ev p (RingHom.id ℂ) U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) ∘ ch.e.symm
        =ᶠ[nhds (ch.e z)] fun _ => c := hn.mono fun v hv => CxPts.ev_algX hv c
    simp only [δ, AddMonoidHom.mk'_apply]
    rw [e.fderiv_eq]
    simp
  exact GlobalTheory.JacSpan.ker_le_span_sup (A := GlobalTheory.CechDR.Sec p U) (CxPts.evHom hz)
    (fun c => (CxPts.ev_eq hz _).symm.trans (CxPts.ev_algX hz c)) δ hmul hc g hgs φ hdet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NullNegEvalOfJacobianDetEqZero
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open MeasureTheory Topology

namespace GlobalTheory.ChartSard

theorem null_negEv_of_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  intro X p d U ch φ
  set T : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap with hT
  have hTw : ∀ w, T w = WithLp.toLp 2 w := fun w => rfl
  set g : Fin d → EuclideanSpace ℂ (Fin d) → ℂ :=
    fun j => GlobalTheory.CxPts.ev p (RingHom.id ℂ) U (φ j) ∘ ch.e.symm with hg
  set H : (Fin d → ℂ) → (Fin d → ℂ) := fun w j => -g j (T w) with hH
  refine ⟨H '' {w | DifferentiableAt ℝ H w ∧ (fderiv ℝ H w).det = 0},
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun w => fderiv ℝ H w)
      (fun w hw => hw.1.hasFDerivAt.hasFDerivWithinAt) (fun w hw => hw.2), ?_⟩
  intro z hzs hz hdet
  set w : Fin d → ℂ := (ch.e z).ofLp with hw
  have hTz : T w = ch.e z := rfl
  have hL : ∀ j, HasFDerivAt (g j) (fderiv ℂ (g j) (ch.e z)) (T w) := fun j => by
    rw [hTz]; exact (ch.differentiableAt_ev (φ j) hzs hz).hasFDerivAt
  set M : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun j => -((fderiv ℂ (g j) (ch.e z)).comp T) with hM
  have hHM : HasFDerivAt H M w := by
    refine hasFDerivAt_pi'.2 fun j => ?_
    exact ((hL j).comp w T.hasFDerivAt).neg
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hTv : T v = ∑ b, v b • EuclideanSpace.single b (1 : ℂ) := by
    ext i
    simp [hTw, EuclideanSpace.single_apply, Pi.single_apply]
  have hMv : M v = 0 := by
    funext j
    have hj := congrFun hv j
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hj
    simp only [hM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, hTv, map_sum, map_smul, smul_eq_mul, Pi.zero_apply, neg_eq_zero]
    rw [← hj]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨w, ⟨(hHM.restrictScalars ℝ).differentiableAt, ?_⟩, ?_⟩
  · rw [(hHM.restrictScalars ℝ).fderiv]
    refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨v, ?_, hv0⟩)
    show M v = 0
    exact hMv
  · funext j
    simp only [hH, hg, Function.comp_apply, hTz, ch.e.left_inv hzs, GlobalTheory.CxPts.ev_eq hz]

end GlobalTheory.ChartSard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesLocationOfMembership
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.SerFinished

set_option maxHeartbeats 2000000 in

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  intro hP hL
  refine GlobalTheory.HeightCounting.Up.Model.AtMem.imp (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.exists_local_langlands_place_datum hP hL)
    (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.coefficient_duty_in_place hL) (GlobalTheory.T.central_local_stable_integral hL))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hO, hC, -, -⟩
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    (GlobalTheory.CoefDuty.OPinModel.labFixed_iff c.a).2 hO.lab
  have htame : ∀ D', D' = withLoc c.a.nt.L → ∀ k (v : D'.nd.PlG k),
      ∃ κ : IsLocalRing.ResidueField (D'.nd.plOm.1 (D'.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D'.host.g k),
        TameCoupled (D'.nd.plOm.1 (D'.naut.plGw k v)) κ (D'.ntypes.tg k v)
          (@GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩).gen := by
    rintro _ rfl k v
    exact ⟨c.a.nt.A.grp.kv k v, GlobalTheory.CoefDuty.OPinModel.tame_of_pin hO k v⟩
  refine GlobalTheory.T.serLoc_of_tameCoupled_of_cenLoc' hP.what₂ hP.green hP.zel hP.dz hL (w.D Z) P _ hlab (htame _ c.a.nt.eq) ?_
  rw [hPin.M_eq]
  exact hC

end GlobalTheory.SerFinished
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothSectionsInFunctionField
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem smooth_sections_in_functionField : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [inst' : Algebra ℂ Z'.functionField], Smooth p' → inst' = ffAlg p' → ∀ (W : Z'.Opens), IsAffineOpen W → ∀ (hW : genericPoint Z' ∈ W) (B : Subalgebra ℂ Z'.functionField), (∀ y, y ∈ B ↔ ∃ g : Γ(Z', W), (Z'.presheaf.germ W (genericPoint Z') hW).hom g = y) → Algebra.Smooth ℂ B := by
  intro Z' _ p' inst' hp hinst W hWa hW B hB
  subst hinst
  letI : Algebra ℂ Z'.functionField := ffAlg p'
  let φ : ℂ →+* Γ(Z', W) := (p'.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have h := HasRingHomProperty.appLE @Smooth p' hp ⟨⊤, isAffineOpen_top _⟩ ⟨W, hWa⟩ le_top
  have h' : RingHom.Smooth φ :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.bijective) h
  letI : Algebra ℂ Γ(Z', W) := φ.toAlgebra
  have hs : Algebra.Smooth ℂ Γ(Z', W) := h'
  let g := (Z'.presheaf.germ W (genericPoint Z') hW).hom
  have hg : Function.Injective g := germ_injective_of_isIntegral Z' (genericPoint Z') hW
  have hc : ∀ c : ℂ, g (algebraMap ℂ Γ(Z', W) c) = algebraMap ℂ Z'.functionField c := by
    intro c
    show g (φ c) = _
    simp only [φ, g, Scheme.Hom.appLE, CommRingCat.comp_apply, RingHom.comp_apply]
    show _ = (Z'.presheaf.germ ⊤ (genericPoint Z') trivial).hom ((p'.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl
  let gA : Γ(Z', W) →ₐ[ℂ] Z'.functionField := { g with commutes' := hc }
  let f : Γ(Z', W) →ₐ[ℂ] B := gA.codRestrict B (fun x => (hB _).2 ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => hg (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (hB y.1).1 y.2
    exact ⟨x, Subtype.ext hx⟩
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective f hf)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePoints
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibTrace

theorem trace_quot_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc hk hred h
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJ
  haveI : Module.Finite k (rB k K x {0} ⧸ J) := GlobalTheory.PD.FibFin.finite_quot k K x hc
  haveI : Module.Free k (rB k K x {0} ⧸ J) := Module.Free.of_divisionRing k _
  have hred' : IsReduced (k ⊗[k] (rB k K x {0} ⧸ J)) :=
    isReduced_of_injective (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).toRingHom
      (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).injective
  have key := (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange (O := k) (H := rB k K x {0} ⧸ J) (K := k) hred').2.2
    (Ideal.Quotient.mk J h)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at key
  rw [key]
  have hker : ∀ e : fib k K x, ∀ a ∈ J, e.1 a = 0 := fun e a ha => by
    have : J ≤ RingHom.ker e.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact e.2 j
    exact this ha
  let E : fib k K x ≃ (rB k K x {0} ⧸ J →ₐ[k] k) :=
    { toFun := fun e => Ideal.Quotient.liftₐ J e.1 (hker e)
      invFun := fun φ => ⟨φ.comp (Ideal.Quotient.mkₐ k J), fun j => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        have hm : (⟨_, tco_mem k K x j⟩ : rB k K x {0}) ∈ J := by
          rw [hJ]; exact Ideal.subset_span ⟨j, rfl⟩
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]⟩
      left_inv := fun e => Subtype.ext (AlgHom.ext fun a => rfl)
      right_inv := fun φ => by
        apply Ideal.Quotient.algHom_ext
        rfl }
  rw [← finsum_comp_equiv E]
  rfl

end GlobalTheory.PD.FibTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

variable (d : ℕ)

theorem X_mem_one (i : Fin (d + 1)) : (X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ 1 :=
  isHomogeneous_X ℂ i

abbrev chart (i : Fin (d + 1)) : (PSpace ℂ d).Opens := Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)

def ratioSec (i j : Fin (d + 1)) : Γ(PSpace ℂ d, chart d i) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)
    (Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j))

variable {d} {Z : Scheme.{0}} [IsIntegral Z]

open Classical in

def rat (φ : Z ⟶ PSpace ℂ d) (i j : Fin (d + 1)) : Z.functionField :=
  if h : genericPoint Z ∈ φ ⁻¹ᵁ chart d i then
    Z.presheaf.germ (φ ⁻¹ᵁ chart d i) (genericPoint Z) h (φ.app (chart d i) (ratioSec d i j))
  else 0

variable [Algebra ℂ Z.functionField]

def fld (φ : Z ⟶ PSpace ℂ d) : IntermediateField ℂ Z.functionField := IntermediateField.adjoin ℂ (Set.range (rat φ 0))

def crd (φ : Z ⟶ PSpace ℂ d) : Fin (d + 1) → fld φ := fun j =>
  ⟨rat φ 0 j, IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩⟩

theorem crd_val (φ : Z ⟶ PSpace ℂ d) (j : Fin (d + 1)) : ((crd φ j : fld φ) : Z.functionField) = rat φ 0 j := rfl

end GlobalTheory.PD.XCover
end
end

