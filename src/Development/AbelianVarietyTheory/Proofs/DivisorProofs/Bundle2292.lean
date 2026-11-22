import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarySplittingTransportedDoubledWeilDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem actAB_one_reG (e : γ ≃ β) {JA : Matrix α α E} {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e)
    (g : GlobalTheory.WeilM.UG c J) (w : Matrix α β E) :
    GlobalTheory.WeilM.actAB c ((1 : GlobalTheory.WeilM.UG c JA), reG c e h g) (w.submatrix id e) =
      (GlobalTheory.WeilM.actB c g w).submatrix id e := by
  simp only [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, reG_val, OneMemClass.coe_one, Units.val_one, Matrix.one_mul,
    Matrix.transpose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _ _ _

theorem continuous_reG [TopologicalSpace E] (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E}
    (h : J' = J.submatrix e e) : Continuous (reG c e h) := by
  unfold reG
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom ?_).comp continuous_subtype_val
  exact (continuous_id (X := Matrix β β E)).matrix_reindex e.symm e.symm

end Gen

section Read

variable {D : D7} [Invertible (2 : AF D.host.F)]

theorem dblD_rho_eq {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ψ : AddChar (AF D.host.F) ℂ) (w : Matrix (Fin T.rank) (Fin S.rank ⊕ Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (dblD _ co).rho ψ w = (ddr co).rho ψ (w.submatrix id finSumFinEquiv.symm) := by
  unfold GlobalTheory.WeilM.Darboux.rho ddr
  rw [reD_e, Matrix.submatrix_submatrix]
  simp

end Read

end GlobalTheory.DblSchr

namespace GlobalTheory.DblSchr

set_option maxHeartbeats 1000000 in

theorem isUSplitting_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co)
            (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r1 : ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank := GlobalTheory.Core.Rk.IP.FockModel.resEta_one_dbl S rT
  have hξd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hξ
  have hrat := GlobalTheory.DblSchr.ddr_rat D S T JA JB ξ κ co hco
  obtain ⟨hpres, himpl⟩ := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hadm := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hunit := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hcont := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hom : ∀ g, omdOf omd₀ g = omd₀ (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) := fun _ => rfl
  refine { pres := ?_, impl := ?_, adm := ?_, unit := ?_, cont := ?_ }
  · intro g φ hφ
    rw [hom]
    exact hpres _ φ hφ
  · intro g w φ hφ
    have e1 := dblD_rho_eq co ψ w
    have e2 := dblD_rho_eq co ψ (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) g w)
    have e3 := himpl (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) (w.submatrix id finSumFinEquiv.symm) φ hφ
    have e4 := actAB_one_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (JA := incM D.host.F JA) (incM_JBd S JB) g w
    rw [e4] at e3
    rw [hom]
    exact (congrArg (fun f => omd₀ _ (f φ)) e1).trans (e3.trans (congrFun e2 _).symm)
  · intro g l hl
    rw [hom]
    exact hadm _ l hl
  · exact hunit.comp _
  · have hr := continuous_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB)
    have hp : Continuous fun g => ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)),
        reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB) g) := continuous_const.prodMk hr
    intro l hl φ hφ
    exact Continuous.congr ((hcont l hl φ hφ).comp hp) (fun g => rfl)

end GlobalTheory.DblSchr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem eq_refl_of_isometry_congMod : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) →
    ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  intro X _ _ _ β hpos e he N hN hc
  choose u hu using hc
  have hQ0 : ∀ x, 0 ≤ β x x := fun x => by
    by_cases h : x = 0
    · simp [h]
    · exact (hpos x h).le
  have hdec : ∀ x, x ≠ 0 → β (u x) (u x) < β x x := by
    intro x hx
    have h1 : 0 ≤ β (e x + x) (e x + x) := hQ0 _
    have h2 : β (e x - x) (e x - x) = (N : ℤ) * ((N : ℤ) * β (u x) (u x)) := by
      rw [show e x - x = N • u x by rw [hu x]; abel]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, he x x] at h1 h2
    have hc := hpos x hx
    have hd := hQ0 (u x)
    have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul hN' hN' (by norm_num) (by omega)) hd]
  have hnil : ∀ n : ℕ, ∀ x, (β x x).toNat = n → ∃ k, u^[k] x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn
      by_cases hx : x = 0
      · exact ⟨0, by simpa using hx⟩
      · have hlt := hdec x hx
        have hd := hQ0 (u x)
        obtain ⟨k, hk⟩ := ih (β (u x) (u x)).toNat (by omega) (u x) rfl
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
  ext y
  by_contra hne
  have huy : u y ≠ 0 := fun h => hne (by rw [hu y, h]; simp)
  classical
  have hex : ∃ k, u^[k] y = 0 := hnil _ y rfl
  have hk : u^[Nat.find hex] y = 0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, u^[j] y ≠ 0 := fun j hj => Nat.find_min hex hj
  have hy0 : y ≠ 0 := fun h => hne (by simp [h])
  have hk2 : 2 ≤ Nat.find hex := by
    by_contra h
    interval_cases h' : Nat.find hex
    · exact hy0 (by simpa using hk)
    · exact huy (by simpa using hk)
  have hux : u (u^[Nat.find hex - 2] y) ≠ 0 := by
    rw [← Function.iterate_succ_apply' u]
    exact hmin _ (by omega)
  have huux : u (u (u^[Nat.find hex - 2] y)) = 0 := by
    rw [← Function.iterate_succ_apply' u, ← Function.iterate_succ_apply' u]
    rw [show (Nat.find hex - 2).succ.succ = Nat.find hex by omega]
    exact hk
  set x := u^[Nat.find hex - 2] y
  have key := he x (u x)
  rw [hu x, hu (u x), huux] at key
  simp only [smul_zero, add_zero, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at key
  have hp := hpos (u x) hux
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith [mul_pos hN0 hp]

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VanishEmbedded

open GlobalTheory.HSCore.VanishNumberField

theorem subsingleton_coh_canon_tens : GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → ∀ (F : Type) [Field F], Nonempty (F →+* ℂ) → ∀ (X : Scheme.{0}) (p : X ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef F N) → (letI := algebraΓOfHom p; IsBig F N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hNum hNad F _ ⟨σ⟩ X p D hsm hp hgc K N hnef hbig q hq
  letI := σ.toAlgebra
  let X' := pullback p (spMap (algebraMap F ℂ))
  let π : X' ⟶ X := pullback.fst _ _
  let p' : X' ⟶ Sp ℂ := pullback.snd _ _
  have H : IsPullback π p' p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hI, -, hsm', hp', -⟩ := GlobalTheory.BaseChangeVariety.baseChange_props F ℂ X X' p p' π D H hp hgc
  haveI : Nonempty X := ⟨π (Classical.arbitrary X')⟩
  letI := algebraΓOfHom p
  letI := algebraΓOfHom p'
  obtain ⟨hprop, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hL := LB.isLB_pull hnef.isLB π
  have hnef' : IsNef ℂ (N.pull π) := GlobalTheory.NefFieldExt.isNef_baseChange hNum F ℂ X X' p p' π H hp N hnef
  have hbig' : IsBig ℂ (N.pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hbig.3
    have hD : topologicalKrullDim X = D := topologicalKrullDim_eq_of_smooth p D hsm
    obtain rfl : D₀ = D := by exact_mod_cast hD₀.symm.trans hD
    refine (isBig_iff (f := p') (fun _ => rfl) hp'
      (topologicalKrullDim_eq_of_smooth _ D₀ hsm')).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hbig.1, cls_pull (isLB_lbPow hbig.1 m), cls_lbPow hbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull H (isLB_lbPow hbig.1 m) 0).symm
  have hKV := GlobalTheory.T.kawamataViehweg_vanishing_of_nadel_pairs hNad X' p' D hp' hI (K.baseChange H) (N.pull π) hnef' hbig' q hq
  have hM : (tens K.bundle N).IsLB := isLB_tens K.isLB hnef.isLB
  have hK' := LB.isLB_pull K.isLB π
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X') (LB.isLB_pull hM π) (isLB_tens hK' hL)
    (by rw [cls_pull hM π, cls_tens K.isLB hnef.isLB, cls_tens hK' hL, cls_pull K.isLB π, cls_pull hnef.isLB π, map_add])
  exact subsingleton_coh_of_pull (f := p) (f' := p') H hM q
    ((cohOn.mapIso Γ(X', ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 hKV)

end GlobalTheory.VanishEmbedded
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionImageFinHomMulVec
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CovTop.VolUp.RatStab

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (V : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V) (δ : GL (Fin V.rank) D.host.E), (hat (maximalRealSubfield D.host.E) (L : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) = ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).mulVec '' (hat (maximalRealSubfield D.host.E) (Λ : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) → IsUStab (-(V.gram)ᵀ) L δ → ∃ γ ∈ GQ V, (∀ τ θ, IsInfEmb τ θ → infMat D.sp.cm.sig V.gram θ γ = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ) ∧ IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (Λ : Set (Fin V.rank → D.host.E)) 1 ((finHom V (g⁻¹ * γ * g)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V Λ L g δ hhat hδ
  have : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨γ₀, hQ, hfin, harch⟩ := GlobalTheory.RepConv.exists_rat V δ hδ.1
  refine ⟨γ₀, hQ, fun τ θ hθ => harch τ θ hθ, ?_⟩
  have hLδ : ∀ x ∈ L, ∃ y ∈ L, (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = (1 : ℕ) • y :=
    fun x hx => ⟨_, sub_mem ((hδ.2 x).1 hx) hx, by simp⟩
  have hLδi : ∀ x ∈ L, ∃ y ∈ L, ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = (1 : ℕ) • y := by
    intro x hx
    have hx' : ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x ∈ L := by
      rw [hδ.2]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact hx
    exact ⟨_, sub_mem hx' hx, by simp⟩
  have hf : (finHom V (g⁻¹ * γ₀ * g)).1 =
      ((finHom V g)⁻¹).1 * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1 := by
    rw [← hfin]
    simp only [map_mul, map_inv, Units.val_mul]
  have hfi : (finHom V (g⁻¹ * γ₀⁻¹ * g)).1 =
      ((finHom V g)⁻¹).1 * ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1 := by
    have hfin' : ((finHom V γ₀)⁻¹).1 = ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) := by
      apply Units.inv_eq_of_mul_eq_one_left
      rw [hfin, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [← hfin']
    simp only [map_mul, map_inv, Units.val_mul]
  have c1 := GlobalTheory.RepConv.hat_cong_conj (F := D.host.F) (Λ : Set (Fin V.rank → D.host.E))
      (L : Set (Fin V.rank → D.host.E)) (finHom V g) hhat δ.1 1 hLδ
  have c2 := GlobalTheory.RepConv.hat_cong_conj (F := D.host.F) (Λ : Set (Fin V.rank → D.host.E))
      (L : Set (Fin V.rank → D.host.E)) (finHom V g) hhat (δ⁻¹ : GL (Fin V.rank) D.host.E).1 1 hLδi
  refine ⟨GlobalTheory.FinUA.isUA_finHom D V _, ?_, ?_⟩
  · intro x hx
    rw [hf]
    exact c1 x hx
  · intro x hx
    obtain ⟨y, hy, e⟩ := c2 x hx
    refine ⟨(finHom V (g⁻¹ * γ₀⁻¹ * g)).1 *ᵥ x, ?_, ?_⟩
    · rw [hfi]
      have : (((finHom V g)⁻¹).1 * ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1) *ᵥ x = x + (1 : ℕ) • y := by
        rw [← e]; abel
      rw [this]; exact add_mem hx (by simpa using hy)
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
      have : g⁻¹ * γ₀ * g * (g⁻¹ * γ₀⁻¹ * g) = 1 := by group
      rw [this, map_one, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.CovTop.VolUp.RatStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureBaseChangeLabelsTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStructure_baseChange_labels_torsion : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  first | exact @GlobalTheory.levelPoint_baseChange_label | exact GlobalTheory.levelPoint_baseChange_label | (intros; apply GlobalTheory.levelPoint_baseChange_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvr
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankUnif

theorem card_eq_g : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) (n : ℕ) (y : Fin n → (epsR V ⟶ G)), IsLieBasis y → n = A.g := by
  intro V _ _ _ D A G _ _ U n y hy
  have := U.smooth
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  obtain ⟨φ, gp⟩ : ∃ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ :=
    ⟨_, ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl⟩
  obtain ⟨v, hv, -⟩ := GlobalTheory.exists_isLieBasis_baseChange V (FractionRing V) (algebraMap V _) G A.A φ gp U.smooth n y hy
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis A.A A.smoothDim
  exact GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis gp hv hv₀

end GlobalTheory.LieRankUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocusStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (L : LB Y) (σ : L.Sec) (z : Sp K ⟶ Y) (i : L.ι) (hi : ⊤ ≤ z ⁻¹ᵁ L.U i), (H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) ≠ 0 ↔ z (IsLocalRing.closedPoint K) ∈ nonzeroLocus σ) := by
  first | exact @GlobalTheory.ValNe.val_ofSec_ne_zero_iff | exact GlobalTheory.ValNe.val_ofSec_ne_zero_iff | (intros; apply GlobalTheory.ValNe.val_ofSec_ne_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationUnitsCharts
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem unitChartAt_of_dvd : ∀ (p n : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (J : Type) (Q : J → R)
    (u : ∀ j, (Localization.Away ((p : R) * Q j))ˣ),
    (∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) → (∃ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖) ∧
      ∀ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖ → ∀ ψ : Localization.Away ((p : R) * Q j) →+* ℂ_[p],
        ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
          ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (u j) - κ‖ < ‖κ‖) →
    (∀ yb' : Sp 𝓞_ℂ_[p] ⟶ X', IsTest p (π ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ π)) →
    ∀ (R' : Type) [CommRing R'] (χ : Sp R' ⟶ X') (g : R →+* R') (x' : X'), IsOpenImmersion χ → x' ∈ Set.range χ →
      χ ≫ π = spMap g ≫ ξ →
      (((π ⁻¹ᵁ Xw : X'.Opens) : Set X').Nonempty → ∃ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ)) →
      ((∃ k, (∀ j, g (Q k) ∣ g (Q j)) ∧ g (Q k) ∣ (p : R') ^ n) ∨ ∀ j, (p : R') ^ n ∣ g (Q j)) →
      UnitChartAt p (π ⁻¹ᵁ Xw) (fun yb' => K (yb' ≫ π)) x' := by
  intro p n _ X X' π Xw K R _ ξ J Q u hC hT R' _ χ g x' hχ hx' hχπ _hD hcase
  have hcomp : ∀ φ : R' →+* 𝓞_ℂ_[p], (spMap φ ≫ χ) ≫ π = spMap (φ.comp g) ≫ ξ := by
    intro φ; rw [Category.assoc, hχπ, sp_sp]
  have hm : ∀ x : 𝓞_ℂ_[p], ‖(x : ℂ_[p])‖ ≤ 1 := fun x => by
    have this : (Valued.v (x : ℂ_[p]) : NNReal) ≤ 1 := x.2
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).2 this
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have htest : ∀ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ) →
      IsTest p Xw (spMap (φ.comp g) ≫ ξ) := by
    intro φ h; rw [← hcomp]; exact hT _ h
  rcases hcase with ⟨k, hk, hkp⟩ | hall
  · have hunit : IsUnit ((algebraMap R' (Localization.Away (p : R'))).comp g ((p : R) * Q k)) := by
      obtain ⟨d, hd⟩ := hkp
      have h1 : IsUnit (algebraMap R' (Localization.Away (p : R')) ((p : R') ^ (n + 1))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (p : R')).pow _
      refine isUnit_of_dvd_unit ⟨algebraMap R' _ d, ?_⟩ h1
      simp only [RingHom.comp_apply, map_mul, map_natCast]
      rw [pow_succ', hd, map_mul, map_mul, map_natCast]; ring
    let L := IsLocalization.Away.lift (S := Localization.Away ((p : R) * Q k)) ((p : R) * Q k) hunit
    refine ⟨R', inferInstance, χ, Units.map L.toMonoidHom (u k), hχ, hx', ?_⟩
    intro φ hφ ψ hψ κ hκ
    obtain ⟨⟨j, hj⟩, hcl⟩ := hC (φ.comp g) (htest φ hφ)
    have hkbig : (p : ℝ)⁻¹ ^ n < ‖((φ.comp g) (Q k) : ℂ_[p])‖ := by
      refine hj.trans_le ?_
      obtain ⟨d, hd⟩ := hk j
      have e : (((φ.comp g) (Q j) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((φ.comp g) (Q k) : ℂ_[p]) * (φ d : ℂ_[p]) := by
        rw [RingHom.comp_apply, hd, map_mul]; rfl
      rw [e, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hm _)
    have hcompat : (ψ.comp L).comp (algebraMap R (Localization.Away ((p : R) * Q k))) =
        (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp g) := by
      ext r
      have := RingHom.congr_fun hψ (g r)
      simp only [RingHom.comp_apply] at this ⊢
      rw [← this]
      congr 1
      exact IsLocalization.lift_eq _ r
    have hκ' : κ ∈ K (spMap (φ.comp g) ≫ ξ) := by rw [← hcomp]; exact hκ
    exact hcl k hkbig (ψ.comp L) hcompat κ hκ'
  · refine ⟨R', inferInstance, χ, 1, hχ, hx', ?_⟩
    intro φ hφ
    exfalso
    obtain ⟨⟨j, hj⟩, -⟩ := hC (φ.comp g) (htest φ hφ)
    obtain ⟨d, hd⟩ := hall j
    have e : (((φ.comp g) (Q j) : 𝓞_ℂ_[p]) : ℂ_[p]) = (p : ℂ_[p]) ^ n * (φ d : ℂ_[p]) := by
      rw [RingHom.comp_apply, hd, map_mul, map_pow, map_natCast]; push_cast; rfl
    rw [e, norm_mul, norm_pow, hpn] at hj
    have := mul_le_of_le_one_right (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg p) : (0:ℝ) ≤ (p : ℝ)⁻¹) n) (hm (φ d))
    linarith

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBoundsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  first | exact @GlobalTheory.OneMeasDim.log_dimAt_le | exact GlobalTheory.OneMeasDim.log_dimAt_le | (intros; apply GlobalTheory.OneMeasDim.log_dimAt_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) (la : Wt X.Ψ N) (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → X.Ψ → Fin (N - X.p0) → ℂ) (Lm : Fin n → X.Ψ → Fin X.p0 → ℂ), IsOrbit X T M γ x → ((∀ j (τ : X.Ψ) (i : Fin (N - X.p0)), Tendsto (fun w => perFr X (x w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : X.Ψ) (i : Fin X.p0), Tendsto (fun w => perFr X (x w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤) → (∀ (u : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr X (x w) u ρ i‖ ≤ C * w.im ^ B) → ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.nfac_inv_le_pow_of_isOrbit_of_perBound | exact GlobalTheory.nfac_inv_le_pow_of_isOrbit_of_perBound | (intros; apply GlobalTheory.nfac_inv_le_pow_of_isOrbit_of_perBound <;> assumption)
end

