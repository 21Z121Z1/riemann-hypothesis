import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0598
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.RowVac

set_option synthInstance.maxHeartbeats 400000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

private lemma eToEAf_mem_hatL_of_mem {n : ℕ} (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (s : Fin n → D.host.E) (hs : s ∈ C) :
    (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem fwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (hb _).1 (eToEAf_mem_hatL_of_mem C s hs)

set_option maxHeartbeats 1000000 in

theorem bwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) C := by
  apply GlobalTheory.MovedHomLat.bwd V k C s
  rw [GlobalTheory.MovedHomLat.mem_globLat_iff]
  apply (hb _).2
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact eToEAf_mem_hatL_of_mem Λ s hs

theorem isVacO_om (W : G.Weil) (p : Pair T) (hp : p.InRange D.R.m) (g : Formalism.L2.Theta.GA D (G.pS p)) (h : Formalism.L2.Theta.GA D (G.pT p))
    (hg : g ∈ GfC (G.pS p)) (hh : h ∈ GfC (G.pT p)) (AS BS : Set (Fin (G.pS p).rank → D.host.E))
    (AT BT : Set (Fin (G.pT p).rank → D.host.E))
    (hact : ∀ w' ∈ latO _ _ BS BT (fun _ => True), ∃ w ∈ latO _ _ AS AT (fun _ => True), actO _ _ g h w = w')
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) AS AT f) :
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) BS BT (W.om p (g, h) f) := by
  have hW := W.om_is p hp
  unfold IsVacO at hf ⊢
  obtain ⟨hstd, hvac⟩ := hf
  obtain ⟨hθ, hth, hlat, hfock, hnrm⟩ := hvac
  obtain ⟨-, -, -, -, -, hpres, hint, -, -, hunit, -⟩ := hW
  have hth' := hpres (g, h) f hth
  have ⟨_, _, hc, _⟩ := hth
  have ⟨_, _, hc', _⟩ := hth'
  refine ⟨hstd, hθ, hth', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hact u hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hint g h _ f hth, hlat.1 w hw]
  · intro e he u hu hhalf
    obtain ⟨w, hw, rfl⟩ := hact u hu
    have hw' : IsHalf e w := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e g⁻¹ h⁻¹ hhalf
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hint g h _ f hth, hlat.2 e he w hw hw']
  · intro τ
    have hg1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg τ
    have hh1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hh τ
    have hgi : compAt W.θ τ (Formalism.L2.Theta.mt _ g⁻¹) = 1 := by
      have := GlobalTheory.WeilVacMove.compAt_mt_mul_inv W.θ τ _ g
      rwa [hg1, one_mul] at this
    have key : ∀ z', W.om p (g, h) (Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' f) =
        Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' (W.om p (g, h) f) := by
      intro z'
      have := GlobalTheory.WeilVacMove.om_dRho (W.om_is p hp) hθ g h τ z' hth
      rwa [hh1, hgi, Matrix.one_mul, Matrix.mul_one] at this
    have h0 := hfock τ
    unfold IsFockVacAt at h0 ⊢
    intro z
    have h1 := h0 z
    unfold annih at h1 ⊢
    rw [← key, ← key, ← map_smul, ← map_add, h1, map_zero]
  · refine ⟨hnrm.1, fun a ha => ?_⟩
    have h1 : nrm2 a.1 a.2 f = 1 := hnrm.2 a ha
    show nrm2 a.1 a.2 _ = 1
    unfold IsCovolOne at ha
    obtain ⟨hμ, hF, -⟩ := ha
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc] at h1
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc', hunit a.1 a.2 hμ hF (g, h) f hth]
    exact h1

theorem neg_mem_GfC (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  unfold GfC at hg ⊢
  rw [MonoidHom.mem_ker] at hg ⊢
  exact hg

set_option maxHeartbeats 1000000 in

theorem moved_isVac (W : G.Weil) (N : Std G U) (Z : Normal W N) (i : ℕ) (hi : i < D.R.m) :
    W.IsVac (.chi i D.R.m) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (N.u (Pair.chi i D.R.m : Pair T).small).1
      (N.u (Pair.chi i D.R.m : Pair T).big).1) (Z.vac (.chi i D.R.m))) := by
  have hdp : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hbig : DefNode D.R.m (Node.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
  have hsmall : DefNode D.R.m (Node.grid i D.R.m) := ⟨hi.le, rfl⟩
  have hp : (Pair.chi i D.R.m : Pair T).InRange D.R.m := ⟨hi, le_rfl⟩
  have hU := N.u_lat _ hbig
  have hV := N.u_lat _ hsmall
  have hg : negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1 ∈ GfC (negSp (G.V (.grid (i + 1) D.R.m))) :=
    neg_mem_GfC (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).2
  have hh : (N.u (.grid i D.R.m)).1 ∈ GfC (G.V (.grid i D.R.m)) := (N.u (.grid i D.R.m)).2
  have hv := Z.vac_is _ hdp
  have hact : ∀ w' ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (G.latS (.chi i D.R.m) : Set _)
      (G.latT (.chi i D.R.m) : Set _) (fun _ => True), ∃ w ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m))
      (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) (fun _ => True),
      actO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1)
        (N.u (.grid i D.R.m)).1 w = w' := by
    refine (GlobalTheory.MovedHomLat.actO_latO_onto _ _ _ _ (N.latS (.chi i D.R.m)) (G.latS (.chi i D.R.m))
      (N.latT (.chi i D.R.m)) (G.latT (.chi i D.R.m)) ?_ ?_ ?_ ?_).2
    · intro s hs
      rw [mt_negGA]
      exact fwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact fwd_gen _ _ _ _ hV t ht
    · intro s hs
      rw [← map_inv, mt_negGA]
      exact bwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact bwd_gen _ _ _ _ hV t ht
  exact isVacO_om W (.chi i D.R.m) hp _ _ hg hh _ _ _ _ hact _ hv

private lemma sigOK_and_isSelfDualC_grid {μ₀ : T} (hL : L.Is μ₀) (a b : ℕ) (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) :
    (G.V (.grid a b)).SigOK ∧ IsSelfDualC (G.V (.grid a b)) (G.Λ (.grid a b)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · show (columnBlock L b).sp.SigOK ∧ IsSelfDualC (columnBlock L b).sp (columnBlock L b).lat
    rcases lt_or_eq_of_le hb with hb' | rfl
    · rw [colY_lt L hb']
      exact ⟨D.sp.Y_sig _, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY b hb')⟩
    · rw [colY_m L]
      exact ⟨D.sp.X'_sig, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX⟩
  · have hv := G.isV (X := .grid a b) ⟨ha, hb⟩ (by intro j h; injection h with h1 h2; omega)
    exact ⟨hv.sigOK, hv.sd⟩

theorem isVac_unique (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hp : (Pair.chi i j : Pair T).InRange D.R.m) {f f'}
    (hf : W.IsVac (.chi i j) f) (hf' : W.IsVac (.chi i j) f') : ∃ κ : ℂˣ, f' = (κ : ℂ) • f := by
  unfold GridData.Weil.IsVac at hf hf'
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hs1, hd1⟩ := sigOK_and_isSelfDualC_grid hL (i + 1) j hp1 hp2
  obtain ⟨hs2, hd2⟩ := sigOK_and_isSelfDualC_grid hL i j (by omega) hp2
  have key := VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.GridWeil.sigOK_neg hs1) hs2
    (fun τ => GlobalTheory.ChiGrid.isCartanInv_neg (W.cart_is (.grid (i + 1) j) ⟨hp1, hp2⟩ τ))
    (W.cart_is (.grid i j) ⟨by omega, hp2⟩) _ _
    (isSelfDualC_neg hd1) hd2 f f' hf hf'
  obtain ⟨c, hc, hcf⟩ := key
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  exact ⟨Units.mk0 c hc0, hcf⟩

theorem moved_vac_eq : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ i : ℕ, i < D.R.m → ∃ κ : ℂˣ, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ch.S.N.u (Pair.chi i D.R.m : Pair T).small).1 (ch.S.N.u (Pair.chi i D.R.m : Pair T).big).1) (ch.S.Z.vac (.chi i D.R.m)) = (κ : ℂ) • ch.rm.vX i D.R.m := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch i hi
  have hL : R.toLevCh.Is A.μ0 := by
    obtain ⟨-, -, -, -, hcore, -⟩ := hS
    exact hcore.lev
  exact isVac_unique ch.W hL i D.R.m ⟨hi, le_rfl⟩ (ch.rm.vX_is i D.R.m hi le_rfl)
    (moved_isVac ch.W ch.S.N ch.S.Z i hi)

end GlobalTheory.RowVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitSum
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealActs Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
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

private def indMap {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

private theorem indMap_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    indMap π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [indMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl

private theorem acts_zero' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

theorem polZero_cpt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W Bs.emb, ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, k) Φ) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM k hk Φ hZ
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hZ
  have hTr := hM.triple
  have hPV : IsPair Bs G.M Xc.β (Xc.β / Xc.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨hTr.base, hTr.geo.hV, hTr.geo.hW, hTr.geo.hM, hTr.chars.heckeβ,
      hecke_div hTr.chars.heckeβ hTr.chars.heckeα, hTr.chars.resβ,
      resEta_div hTr.chars.resβ hTr.chars.resα rfl, hTr.weil⟩
  have actV := GlobalTheory.T.polynomial_datum_action_of_pair hP F E σ Bs a (a + a') G.V G.W G.M _ _ om _ _ _ _ hPV
  obtain ⟨D, hDm, hDi⟩ := actV.2.2.2 k hk
  have hA : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, Acts (evI F) (⇑(om (1, k))) (⇑g) (⇑(D g)) := fun g hg =>
    (hDi g hg (D g)).2 rfl

  have hpure : ∀ i, om (1, k) (pure (f i) (φ i)) = pure (D (f i)) (φ i) := by
    intro i
    have hstd : ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [T.finite_toSet.compl_mem_cofinite, hTr.geo.hM.std] with v hv hv'
      rw [(hf i).2.2 v hv, hv']
    exact hA (f i) (hf i).1 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 hstd)

  let N := G.M.Pol Bs.ψ Bs.emb
  let π : N →ₗ[ℂ] R.Pi := R.p ∘ₗ N.subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ N.map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ u : N, π u = 0 → π ((D.restrict hDm) u) = 0 := by
    intro u hu
    have := hM.real.cpt k hk u.1 u.2 0 (zero_mem _) (D u.1) 0 (hA u.1 u.2) (acts_zero' _)
      (by rw [map_zero]; exact hu)
    rw [map_zero] at this
    exact this
  let ρ := indMap π hπ (D.restrict hDm) ker0
  have hρ : ∀ i, R.p (D (f i)) = ρ (R.p (f i)) := fun i =>
    (indMap_apply π hπ (D.restrict hDm) ker0 ⟨f i, (hf i).1⟩).symm
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure i
  · have := congrArg (LinearMap.rTensor _ ρ) hz
    rw [map_sum, map_zero] at this
    simpa only [LinearMap.rTensor_tmul, hρ] using this

end GlobalTheory.PolKerCpt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
noncomputable section

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mulL {d : ℕ} (c : E) : (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) where
  toFun z := fun j => inclR (F := F) (AF F) c * z j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma mulL_apply {d : ℕ} (c : E) (z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (j : Fin d) :
    mulL (F := F) c z j = inclR (F := F) (AF F) c * z j := rfl

lemma mulL_int_mem {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (o : 𝓞 E)
    {z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : mulL (F := F) (o : E) z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    simp only [mulL_apply, Pi.smul_apply]
    rw [Algebra.smul_def (A := E) o (y j), map_mul, mul_smul_comm]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rowL {n d : ℕ} (i₀ : Fin n) (c : E) :
    Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) where
  toFun Γ := fun j => inclR (F := F) (AF F) c * Γ i₀ j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma rowL_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (i₀ : Fin n) (c : E)
    (hc : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀)
    {Γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)} (hΓ : Γ ∈ latAtV X W v) :
    rowL (F := F) i₀ c Γ ∈ GlobalTheory.InertSph.latAt W v := by
  induction hΓ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨o, ho⟩ := hc x hx
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    show inclR (F := F) (AF F) c * (a • incM F (Matrix.vecMulVec x y)) i₀ j = _
    simp only [Matrix.smul_apply, Pi.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [Algebra.smul_def (A := E) o (y j), mul_smul_comm, ← map_mul, ← mul_assoc]
    congr 2
    rw [← ho]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

lemma rowL_vecMulVec {n d : ℕ} (i₀ : Fin n) (c : E) (x : Fin n → E) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    rowL (F := F) i₀ c (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) = mulL (F := F) (c * x i₀) q := by
  ext j
  simp only [rowL, mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, map_mul, mul_assoc]

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coefSub {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    Submodule (𝓞 E) E where
  carrier := {c | mulL (F := F) c q ∈ GlobalTheory.InertSph.latAt W v}
  zero_mem' := by
    change mulL (F := F) (0 : E) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (0 : E) q = 0 := by ext j; simp [mulL_apply]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).zero_mem
  add_mem' {a b} ha hb := by
    change mulL (F := F) (a + b) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (a + b) q = mulL (F := F) a q + mulL (F := F) b q := by
      ext j; simp [mulL_apply, add_mul]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).add_mem ha hb
  smul_mem' o c hc := by
    change mulL (F := F) (o • c) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (o • c) q = mulL (F := F) (o : E) (mulL (F := F) c q) := by
      ext j; simp only [mulL_apply, Algebra.smul_def, map_mul, mul_assoc]
    rw [this]; exact mulL_int_mem W v o hc

theorem extract (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (hn : 0 < n) (hL : X.L.IsLattice E)
    (h : ∀ x ∈ X.L, Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v) :
    q ∈ GlobalTheory.InertSph.latAt W v := by
  set i₀ : Fin n := ⟨0, hn⟩
  let b₀ : Submodule (𝓞 E) E := X.L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i₀)
  have hfg : b₀.FG := hL.fg.map _
  let 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨b₀, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ b, b ∈ 𝔟 ↔ ∃ x ∈ X.L, x i₀ = b := fun b => by
    rw [← FractionalIdeal.mem_coe]; exact Submodule.mem_map
  have hne : 𝔟 ≠ 0 := by
    intro h0
    have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) i₀) := by
      rw [Submodule.span_le]
      intro x hx
      have : x i₀ ∈ 𝔟 := (hmem _).2 ⟨x, hx, rfl⟩
      rw [h0, FractionalIdeal.mem_zero_iff] at this
      simpa using this
    rw [hL.span_eq_top] at hle
    have := hle (Submodule.mem_top (x := Pi.single i₀ (1 : E)))
    simp at this
  have hone : (1 : E) ∈ ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
    rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_coe]; exact FractionalIdeal.one_mem_one _
  have hle : ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ coefSub W v q := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro c hc b hb
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hc
    rw [FractionalIdeal.mem_coe, hmem] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hc' : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀ := by
      intro x hx
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hc _ ((hmem _).2 ⟨x, hx, rfl⟩))
      exact ⟨o, ho⟩
    change mulL (F := F) (c * x i₀) q ∈ GlobalTheory.InertSph.latAt W v
    rw [← rowL_vecMulVec]
    exact rowL_mem X W v i₀ c hc' (h x hx)
  have h1 : mulL (F := F) (1 : E) q ∈ GlobalTheory.InertSph.latAt W v := hle hone
  have : mulL (F := F) (1 : E) q = q := by ext j; simp [mulL_apply]
  rwa [this] at h1

end GlobalTheory.LatExtract

theorem GlobalTheory.LatExtract.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), 0 < n → X.L.IsLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := fun F E _ _ _ _ _ n d X W v q hn hL h =>
  GlobalTheory.LatExtract.extract n d X W v q hn hL h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinateSupportIntegralAtLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_support_integral_at_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ (ξ : Matrix (Fin X.rank) (Fin r) D.host.E) (x : Mx D X.rank r),
        x.map (finPart D) = (ξ.map (incA D) : Mx D X.rank r).map (finPart D) → d.mixS X ψ μ' 𝓕' Ψ x 0 ≠ 0 →
        ∀ i j, IsIntegral ℤ (((M * n : ℕ) : D.host.E) * ξ i j) := by
  first | exact @GlobalTheory.MixSupport.mixS_support_integral | exact GlobalTheory.MixSupport.mixS_support_integral | (intros; apply GlobalTheory.MixSupport.mixS_support_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesCuspidalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_series_cuspidal : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  first | exact @GlobalTheory.PoinCusp.poin_isCuspFun | exact GlobalTheory.PoinCusp.poin_isCuspFun | (intros; apply GlobalTheory.PoinCusp.poin_isCuspFun <;> assumption)
end

