import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFiniteOpenSubgroupsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finite_openSubgroups : ∀ (D : D7) (a b : ℕ) (JA : Matrix (Fin a) (Fin a) D.host.E) (JB : Matrix (Fin b) (Fin b) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    ∀ p0 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p
          (co.e.symm (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x', GlobalTheory.WeilCont.adeleJoin D.host.F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) := by
  first | exact @GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D | exact GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D | (intros; apply GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.RealUniq

open GlobalTheory.RealActs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div' {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_V (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div' h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div' h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isPair_V' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div' h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div' h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem det_ne_zero_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

theorem howe_sup (hKP : KP) {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χY χW : Chr F E}
    {o : Rep σ Y W} (h : IsPair B M χY χW o r s r' s') :
    ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N' → N ≠ M.Pol B.ψ B.emb →
      N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hY : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.herm.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hW : W.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.skew.sig w) (by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])
  exact (hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW
    h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan).2

variable {κ : Type} [Fintype κ]

theorem actsD_zero (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem acts_zero (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

def induced {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

theorem induced_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    induced π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [induced, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl

theorem realMaps_unique : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ → ∃ (ψ : R.Pi ≃ₗ[ℂ] R₃.Pi) (l : ℂ), l ≠ 0 ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ (R.p f)) ∧ ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l • ψ (R.p' f) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM R₃ hR₃
  have hR := hM.real
  have hPV := isPair_V hM.triple
  have hPV' := isPair_V' hM.triple
  have actV := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV
  have actV' := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV'
  have ks_p : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M om R'.p := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ f hf 0 (zero_mem _) f₁ 0 h1 (actsD_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this⟩
  have ks_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M' om' R'.p' := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ 0 (zero_mem _) f hf 0 f₁ (actsD_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk 0 (zero_mem _) f hf 0 f₁ (acts_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm⟩
  have onto' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R'.p' f' = y :=
    fun R' h y => by
      have : y ∈ (G.M'.Pol B.ψ B.emb).map R'.p' := h.quot'.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have onto : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f ∈ G.M.Pol B.ψ B.emb, R'.p f = y :=
    fun R' h y => by
      have : y ∈ (G.M.Pol B.ψ B.emb).map R'.p := h.quot.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have irr_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → Irred B G.M' om' R'.p' := fun R' h N h1 h2 => by
    apply h.irred N
    · intro γ hγ f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.1 γ hγ
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.lie γ hγ f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h1 γ hγ f' hf' (D f') h1' (e ▸ hN)
    · intro k hk f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.2 k hk
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.cpt k hk f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h2 k hk f' hf' (D f') h1' (e ▸ hN)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M om _ _ R.p R₃.p actV (howe_sup hKP hPV) hR.quot hR₃.quot hR.nontriv
    hR₃.nontriv (ks_p R hR) (ks_p R₃ hR₃) hR.irred hR₃.irred
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M' om' _ _ R.p' R₃.p' actV' (howe_sup hKP hPV') hR.quot' hR₃.quot'
    hR.nontriv hR₃.nontriv (ks_p' R hR) (ks_p' R₃ hR₃) (irr_p' R hR) (irr_p' R₃ hR₃)
  choose DL hDLm hDLi using actV.2.2.1
  choose DK hDKm hDKi using actV.2.2.2
  choose DL' hDLm' hDLi' using actV'.2.2.1
  choose DK' hDKm' hDKi' using actV'.2.2.2
  let ι : Type := {γ // γ ∈ Lines σ G.W} ⊕ {k // k ∈ KInf σ G.W B.emb}
  let D : ι → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    Sum.elim (fun γ => DL γ.1 γ.2) (fun k => DK k.1 k.2)
  let D' : ι → SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')) :=
    Sum.elim (fun γ => DL' γ.1 γ.2) (fun k => DK' k.1 k.2)
  have Dm : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, D i f ∈ G.M.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm _ _ f hf, hDKm _ _ f hf]
  have Dm' : ∀ i, ∀ f ∈ G.M'.Pol B.ψ B.emb, D' i f ∈ G.M'.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm' _ _ f hf, hDKm' _ _ f hf]
  have joint : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f' ∈ G.M'.Pol B.ψ B.emb, R'.p f = R'.p' f' → R'.p (D i f) = R'.p' (D' i f') := by
    rintro R' h (γ | k) f hf f' hf' e
    · exact h.lie γ.1 γ.2 f hf f' hf' _ _ ((hDLi _ _ f hf _).2 rfl) ((hDLi' _ _ f' hf' _).2 rfl) e
    · exact h.cpt k.1 k.2 f hf f' hf' _ _ ((hDKi _ _ f hf _).2 rfl) ((hDKi' _ _ f' hf' _).2 rfl) e
  have ker0 : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = 0 → R.p (D i f) = 0 := by
    rintro (γ | k) f hf h0
    · exact (ks_p R hR).1 γ.1 γ.2 f hf _ ((hDLi _ _ f hf _).2 rfl) h0
    · exact (ks_p R hR).2 k.1 k.2 f hf _ ((hDKi _ _ f hf _).2 rfl) h0
  let π : G.M.Pol B.ψ B.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol B.ψ B.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨f, hf, e⟩ := onto R hR y
    exact ⟨⟨f, hf⟩, e⟩
  let ρ : ι → Module.End ℂ R.Pi := fun i =>
    induced π hπ ((D i).restrict (Dm i)) (fun u hu => ker0 i u.1 u.2 hu)
  have hρ : ∀ i, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), ρ i (R.p f) = R.p (D i f) := fun i f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have irrρ : ∀ N : Submodule ℂ R.Pi, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN => by
    apply hR.irred N
    · intro γ hγ f hf f₁ h1 hx
      rw [(hDLi γ hγ f hf f₁).1 h1]
      have := hN (Sum.inl ⟨γ, hγ⟩) _ hx
      rwa [hρ _ f hf] at this
    · intro k hk f hf f₁ h1 hx
      rw [(hDKi k hk f hf f₁).1 h1]
      have := hN (Sum.inr ⟨k, hk⟩) _ hx
      rwa [hρ _ f hf] at this
  let T : Module.End ℂ R.Pi := ψ.symm.toLinearMap ∘ₗ ψ₁.toLinearMap
  have comm : ∀ i, T * ρ i = ρ i * T := fun i => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f', hf', rfl⟩ := onto' R hR x
    obtain ⟨f, hf, e⟩ := onto R hR (R.p' f')
    obtain ⟨g, hg, eg⟩ := onto R₃ hR₃ (R₃.p' f')
    have j1 := joint R hR i f hf f' hf' e
    have j3 := joint R₃ hR₃ i g hg f' hf' eg
    have lhs : T (ρ i (R.p' f')) = R.p (D i g) := by
      calc T (ρ i (R.p' f')) = ψ.symm (ψ₁ (R.p' (D' i f'))) := by rw [← e, hρ i f hf, j1]; rfl
      _ = ψ.symm (R₃.p' (D' i f')) := by rw [← hψ₁ _ (Dm' i f' hf')]
      _ = R.p (D i g) := by rw [← j3, hψ _ (Dm i g hg), LinearEquiv.symm_apply_apply]
    have rhs : ρ i (T (R.p' f')) = R.p (D i g) := by
      calc ρ i (T (R.p' f')) = ρ i (ψ.symm (R₃.p' f')) := by
            show ρ i (ψ.symm (ψ₁ (R.p' f'))) = _
            rw [← hψ₁ f' hf']
      _ = ρ i (R.p g) := by rw [← eg, hψ g hg, LinearEquiv.symm_apply_apply]
      _ = R.p (D i g) := hρ i g hg
    rw [Module.End.mul_apply, Module.End.mul_apply, lhs, rhs]
  have hrank : Module.rank ℂ R.Pi ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective π hπ).trans (GlobalTheory.T.polynomial_data_countable_rank hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV)
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank R.Pi ι ρ T hR.nontriv hrank irrρ comm
  have hT : ∀ x, T x = c • x := fun x => by rw [hc]; rfl
  refine ⟨ψ, c, ?_, hψ, fun f hf => ?_⟩
  · rintro rfl
    haveI := hR.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
    have h0 : ψ.symm (ψ₁ x) = 0 := by rw [← zero_smul ℂ x, ← hT x]; rfl
    exact hx (ψ₁.injective (ψ.symm.injective (h0.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  · rw [hψ₁ f hf]
    calc ψ₁ (R.p' f) = ψ (T (R.p' f)) := by
          show _ = ψ (ψ.symm (ψ₁ (R.p' f)))
          rw [LinearEquiv.apply_symm_apply]
    _ = c • ψ (R.p' f) := by rw [hT, map_smul]

end GlobalTheory.ThK.RealUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation

namespace GlobalTheory.SupFull

section Generic

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]

theorem exists_smul_nonneg_of_pow (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (S : Set R)
    (hS : ∀ g ∈ S, ∃ s : K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • g)) (f : R) (k : ℕ)
    (hf : f ^ (k + 1) ∈ Submodule.span K S) : ∃ s : K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • f) := by
  have h1 : Submodule.span K S ≤ Submodule.span K (latIn ⊤ Vs hV : Set R) := by
    refine Submodule.span_le.2 fun g hg => ?_
    obtain ⟨s, hs, h⟩ := hS g hg
    rw [← inv_smul_smul₀ hs g]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latIn _ _ _ _).2 ⟨trivial, h⟩))
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ (h1 hf)
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul K] at ht
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero t.2
  refine ⟨_, ht0, fun la v hv => ?_⟩
  have h2 := ((mem_latIn _ _ _ _).1 ht).2 la v hv
  have hv' := hV la v hv
  rw [hv'.smul _ _ ht0] at h2 ⊢
  by_cases htop : v f = ⊤
  · rw [htop, EReal.coe_add_top]; exact le_top
  obtain ⟨x, hx⟩ : ∃ x : ℝ, v f = x := ⟨_, (EReal.coe_toReal htop (hv'.ne_bot f)).symm⟩
  have h3 : ∀ m : ℕ, v (f ^ (m + 1)) = ((((m : ℝ) + 1) * x : ℝ) : EReal) := fun m => by
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ, hv'.mul, ih, hx, ← EReal.coe_add]
      congr 1; push_cast; ring
  have h4 : (0 : ℝ) ≤ (vAdd la (algebraMap (𝓞 K) K t) : ℤ) := by exact_mod_cast vAdd_int_nonneg la ht0
  rw [h3, ← EReal.coe_add, EReal.coe_nonneg] at h2
  rw [hx, ← EReal.coe_add, EReal.coe_nonneg]
  rcases le_total 0 x with h | h
  · linarith
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (neg_nonneg.2 h)]

theorem fg_latIn (C : Submodule K R) [FiniteDimensional K C] (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : ∀ x ∈ C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (φ : R →ₗ[K] K'),
      φ x ≠ 0 ∧ ∀ y ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v y) → IsIntegral ℤ (φ y)) : (latIn C Vs hV).FG := by
  refine Submodule.FG.map _ (GlobalTheory.fg_of_integral_functionals K C _ fun x hx => ?_)
  obtain ⟨K', _, _, _, φ, h0, h1⟩ := h x.1 x.2 fun e => hx (Subtype.ext e)
  exact ⟨K', inferInstance, inferInstance, inferInstance, φ ∘ₗ C.subtype, h0, fun y hy => h1 y.1 y.2 hy⟩

end Generic

theorem pow_mem_cusp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) (k : ℕ) :
    ∃ a', Dom a' ((k + 1) * n) ∧ f ^ (k + 1) ∈ cusp Xo c U a' ((k + 1) * n) := by
  have hM : CuspMul Xo c U := (Formalism.L2.PjFree.cuspMul_ofPj U).1 (GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c r _)
  induction k with
  | zero => exact ⟨a, by simpa using hd, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨a', h1, h2⟩ := ih
    rw [Nat.succ_mul, pow_succ]
    exact ⟨a' + a, ⟨fun τ => (h1.1 τ).add (hd.1 τ), h1.2.add hd.2⟩, hM _ _ _ _ _ _ h1 hd h2 hf⟩

theorem exists_unf (D : D7) (Q : Par D) (hQ : Q.Pins) (j : ℕ) (hj : InR D j) :
    ∃ U : Formalism.L2.PjFree.Unf (Q.Xo j) Q.c Q.c.F.val.toRingHom D.R.r, Formalism.L2.PjFree.IsUnf U ∧
      (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) ∧ (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) Q.l.M) ∧
      (∀ k la γ, (U.X k).χ la γ = 1) ∧
      ∀ k, ∃ (Xx : DataX D.host.E D.R.r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
        Xx.toData = U.X k ∧ 𝔄 ≠ 0 ∧
        Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  obtain ⟨-, -, hM', -, hx1, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D Q hQ
  obtain ⟨hr, hr1, -⟩ := hnum j hj
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    have : cc (-D.host.xi0) = -cc D.host.xi0 := by simp [cc]
    rw [this, GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D]
  have hneg : ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
    intro τ hτ
    rw [hQ.1.2.1, hQ.1.2.2.1] at hτ
    have h := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [h0]
      simpa using d_pos D
    rw [if_pos hpos, Int.cast_one, one_mul] at h
    simpa using h
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum _ Q.H (Q.Dw j) (-(-D.host.xi0))
    (by rw [neg_neg, GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D]) (by rw [neg_neg]; exact cmHost_imaginaryGenerator_ne_zero hP D) _ hr.symm
  obtain ⟨U, hU, hPr, -, hχ, hG, -⟩ := GlobalTheory.FrameUnif.exists_unf_hasPrinc _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
    Q.c.F.val.toRingHom D.R.r (-D.host.xi0) Gm φ (by omega) rfl hξ hneg hφ
  rw [hM'] at hPr
  refine ⟨U, hU, fun k k' => ⟨(hG k).1.trans (hG k').1.symm, (hG k).2.trans (hG k').2.symm⟩,
    fun k ga hga h => ?_, hχ, fun k => ?_⟩
  · refine hPr k ga hga fun x hx => ?_
    obtain ⟨u, hu, e⟩ := h x hx
    exact ⟨u, hu, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  · have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ _ _ U hU k
    have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (U.X k).ξ0 * D.host.AA *
        D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
      rw [(hG k).2, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact hP D.R D.host
    have hM : 0 < Q.l.M := by have := Q.l.three_le; omega
    obtain ⟨Xx, h1, -, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ (U.X k) D.host.AA D.host.AAbar
      (xiR D) Q.l.M
      (fun a => by
        rw [GlobalTheory.LatticeData.cc_eq_conj]
        exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
      hone (fun τ => by rw [(hG k).2, map_neg, norm_neg]; exact xiConst_holds D τ) hx1 hperf.1 hperf.2 hM (hPr k)
    exact ⟨Xx, _, h1, AA_ne_zero hP D, h3⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem fullAt_of_pins (D : D7) (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j)
    (hU : IsUnf (T.U j T.σ₀)) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) : FullAt T j w := by
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hQ
  obtain ⟨hr, hr1, -⟩ := hnum j hj
  obtain ⟨U', hU', hG, hPr, hχ, hX⟩ := exists_unf D T.Q hQ j hj
  have hbdd : ∀ a n, Dom a n → ∀ f ∈ T.cuspA j a n,
      ∀ k, (U'.X k).IsBddSec (laU U'.toPj a n k) (rdU U'.toPj f k) := fun a n hd f hf =>
    isBddSec_of_isUnf _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀ _ (T.U j T.σ₀) U'.toPj T.good_σ₀ hU hU' (by omega) a n hd f
      (cusp_le_sec _ _ _ _ _ hf) fun k =>
        (Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ (((mem_cusp _ _ _ _ _ f).1 hf).2 _ T.good_σ₀) k).1
  constructor
  · haveI : FiniteDimensional T.Q.c.F (cuspW T j w) :=
      GlobalTheory.cuspForms_finiteDimensional_of_goodEmb _ _ _ _ _ _ _ (T.U j) T.σ₀ T.good_σ₀ hU _ _ (dom_wtA w)
    refine fg_latIn _ _ _ fun x hx hx0 => ?_
    letI := T.Q.H.starRing
    have hs := cusp_le_sec _ _ _ _ _ hx
    obtain ⟨z, La, hz, hG0⟩ := GlobalTheory.CMDetect.exists_good_cmPt_frPoly_ne_zero _ _ _ _ (T.Q.Xo j) T.Q.c (fun _ => rfl) _
      U'.toPj hU' hr1 hX _ _ x hs hx0 (hbdd _ _ (dom_wtA w) x hx)
    obtain ⟨y, N, h0, hint⟩ := GlobalTheory.LatFull.CMInt.exists_frame_bounded_denom _ _ _ _ (T.Q.Xo j) T.Q.c z _ La hz _ _ x
      hs hG0
    refine ⟨z.K, inferInstance, inferInstance, inferInstance,
      { toFun := fun F => N * evR (T.Q.Xo j) T.Q.c F y
        map_add' := fun F G => ?_
        map_smul' := fun s F => ?_ }, h0, fun F hF => hint F (cusp_le_sec _ _ _ _ _ hF)⟩
    · rw [← mul_add]
      exact congrArg _ (evalAt_add _ _ F G y)
    · have e : evR (T.Q.Xo j) T.Q.c (s • F) y = algebraMap T.Q.c.F z.K s * evR (T.Q.Xo j) T.Q.c F y :=
        evalAt_smul _ _ s F y
      rw [e, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
  · refine le_antisymm (Submodule.span_le.2 fun f hf => ((mem_latIn _ _ _ f).1 hf).1) fun f hf => ?_
    obtain ⟨a', hd', hf'⟩ := pow_mem_cusp (T.U j) (dom_wtA w) hf (4 * (Module.finrank ℚ D.host.E * D.R.r) + 3)
    obtain ⟨d, nab, hlev, hnab, hroot, hle, hph, hspan⟩ := exists_datum_span _ _ _ _ (T.Q.Xo j) T.Q.c _ _ U' hr1 hA
      T.good_σ₀ hU' hG hPr a' _ hd' (Nat.le_mul_of_pos_right _ hn) fun k ga _ => hχ k _ ga
    have hsf : Squarefree d.l₂.M := by
      rw [hle, hQ.2.1.1,
        Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
      exact ⟨(D.host.g_prime 0).prime.squarefree, (D.host.g_prime 1).prime.squarefree⟩
    obtain ⟨s, hs, h⟩ := exists_smul_nonneg_of_pow (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) isVal_valSet _
      (exists_smul_short_nonneg D _ _ _ (T.Q.Xo j) T.Q.c _ d hlev hnab hroot hsf hph nab 1 0 a') f _
      (hspan _ (cusp_le_sec _ _ _ _ _ hf') (hbdd _ _ hd' _ hf'))
    rw [← inv_smul_smul₀ hs f]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latIn _ _ _ _).2 ⟨Submodule.smul_mem _ _ hf, h⟩))

end GlobalTheory.SupFull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLeviStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  first | exact @GlobalTheory.CentralLevi.exists_unit_smul_of_central | exact GlobalTheory.CentralLevi.exists_unit_smul_of_central | (intros; apply GlobalTheory.CentralLevi.exists_unit_smul_of_central <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTopOfDictionaryDepthStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_top_of_dictionary_depth : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinTopK := by
  first | exact @GlobalTheory.SumSize.TopInt.finTopK | exact GlobalTheory.SumSize.TopInt.finTopK | (intros; apply GlobalTheory.SumSize.TopInt.finTopK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTraceStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMember_lieAction_fock_plus_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om → ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  first | exact @GlobalTheory.HoweD.LieFirstD.lieFirstD | exact GlobalTheory.HoweD.LieFirstD.lieFirstD | (intros; apply GlobalTheory.HoweD.LieFirstD.lieFirstD <;> assumption)
end

