import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat.PairLatLattice

variable {E : Type} [Field E] [NumberField E]

theorem scLat_isLattice {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.scLat 𝔞 Λ) := by
  have hinv : 𝔞⁻¹ ≠ 0 := inv_ne_zero h𝔞
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hinv)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr h𝔞)
  have hb' : b ∈ 𝔞⁻¹ := hb
  have ha' : a ∈ 𝔞 := ha
  refine ⟨?_, ?_⟩
  ·
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
      (LinearMap.lsmul E (Fin n → E) b⁻¹).restrictScalars (𝓞 E)
    have hle : GlobalTheory.SkewLat.scLat 𝔞 Λ ≤ Λ.map f := by
      intro y hy
      refine ⟨b • y, hy b hb', ?_⟩
      simp [f, smul_smul, mul_inv_cancel₀ hb0]
    exact Submodule.FG.of_le (Submodule.FG.map f hΛ.fg) hle
  ·
    have hmem : ∀ y ∈ Λ, a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
      intro y hy c hc
      have hca : c * a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← inv_mul_cancel₀ h𝔞]
        exact FractionalIdeal.mul_mem_mul hc ha'
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hca
      rw [smul_smul, ← hr, algebraMap_smul]
      exact Λ.smul_mem r hy
    rw [eq_top_iff, ← hΛ.span_eq_top]
    refine Submodule.span_le.mpr fun y hy => ?_
    have h1 : a • y ∈ Submodule.span E (GlobalTheory.SkewLat.scLat 𝔞 Λ : Set (Fin n → E)) :=
      Submodule.subset_span (hmem y hy)
    have h2 := Submodule.smul_mem _ a⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h2

theorem prod_span_eq_top {a b : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsLattice E M) (hN : Submodule.IsLattice E N) :
    Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E))) = ⊤ := by
  set S := Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E)))
  have hl : ∀ x : Fin a → E, (x, 0) ∈ S := by
    have : Submodule.span E (M : Set (Fin a → E)) ≤ S.comap (LinearMap.inl E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show (m, (0 : Fin b → E)) ∈ M.prod N from ⟨hm, N.zero_mem⟩)
    intro x
    have hx : x ∈ Submodule.span E (M : Set (Fin a → E)) := by rw [hM.span_eq_top]; trivial
    exact this hx
  have hr : ∀ y : Fin b → E, (0, y) ∈ S := by
    have : Submodule.span E (N : Set (Fin b → E)) ≤ S.comap (LinearMap.inr E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show ((0 : Fin a → E), m) ∈ M.prod N from ⟨M.zero_mem, hm⟩)
    intro y
    have hy : y ∈ Submodule.span E (N : Set (Fin b → E)) := by rw [hN.span_eq_top]; trivial
    exact this hy
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have := S.add_mem (hl x) (hr y)
  simpa using this

theorem pairLat_isLattice {a b d : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsLattice E M) (hN : Submodule.IsLattice E N) (e : Fin a ⊕ Fin b ≃ Fin d) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat M N e) := by
  let φ : (Fin d → E) ≃ₗ[E] (Fin a → E) × (Fin b → E) :=
    (LinearEquiv.funCongrLeft E E e).trans (LinearEquiv.sumArrowLequivProdArrow _ _ E E)
  have hφ : GlobalTheory.SkewLat.pairLat M N e = (M.prod N).map (φ.symm.restrictScalars (𝓞 E)).toLinearMap := by
    ext x
    rw [Submodule.mem_map_equiv, GlobalTheory.SkewLat.mem_pairLat]
    rfl
  rw [hφ]
  refine ⟨Submodule.FG.map _ (Submodule.FG.prod hM.fg hN.fg), ?_⟩
  rw [Submodule.map_coe]
  have : ⇑(φ.symm.restrictScalars (𝓞 E)).toLinearMap = ⇑φ.symm.toLinearMap := rfl
  rw [this, Submodule.span_image, prod_span_eq_top hM hN, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr φ.symm.surjective

end GlobalTheory.SkewLat.PairLatLattice

open GlobalTheory.SkewLat.PairLatLattice in
theorem GlobalTheory.SkewLat.pairLat_scLat_isLattice : ∀ {E : Type} [Field E] [NumberField E] {a b d : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E}, 𝔞 ≠ 0 →
    ∀ {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}, Submodule.IsLattice E ΛA →
    Submodule.IsLattice E ΛB → ∀ (e : Fin a ⊕ Fin b ≃ Fin d),
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat 𝔞 ΛA) (GlobalTheory.SkewLat.scLat 𝔞 ΛB) e) := by
  intro E _ _ a b d 𝔞 h𝔞 ΛA ΛB hA hB e
  exact pairLat_isLattice (scLat_isLattice h𝔞 hA) (scLat_isLattice h𝔞 hB) e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def coords : Set (Fin p → E) :=
  {c | ∃ n : ℕ, 0 < n ∧ ∃ x : Fin p → 𝓞 E, (∀ a, (x a : E) = n * c a) ∧
    ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)}

def lat : Submodule (𝓞 E) (Fin p → E) := Submodule.span (𝓞 E) (coords X)

theorem isLinearHom_prod (x : Fin p → 𝓞 E) :
    Serre.IsLinearHom (X.A true).t.act X.B.t.act (∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)) := by
  classical
  refine Finset.prod_induction _ (Serre.IsLinearHom (X.A true).t.act X.B.t.act)
    (fun f g hf hg => hf.mul hg) (Serre.IsLinearHom.one _ _) fun a _ => ?_
  exact (Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))

theorem intl_mem (x : Fin p → 𝓞 E) : (fun a => (x a : E)) ∈ lat X :=
  Submodule.subset_span ⟨1, one_pos, x, fun a => by simp, _, isLinearHom_prod X x, pow_one _⟩

end GlobalTheory.FlatCM.HomLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfIntegers
section
noncomputable section

open WittVector CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConstDatum

theorem isLocalRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap O C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap O C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap O C a) (algebraMap O C (1 - a))
  have h4 : algebraMap O C a + algebraMap O C (1 - a) = 1 := by rw [← map_add]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem etale_al (ε : PreTilt O p) (h : ℕ) (y : Fin h → O) : (etale ε h).al y = y := by
  simp [Datum.al, etale, Matrix.map_one _ (map_zero _) (map_one _)]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : fontaineTheta O p (Sandwich.mu ε) = 0 := by
  rw [Sandwich.mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

theorem etale_bb {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) (y : Fin h → O) :
    (etale ε h).bb y = 0 := by
  ext i
  simp [Datum.bb, etale, Matrix.mulVec, dotProduct, theta_mu hε]

theorem etale_Fil {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) : (etale ε h).Fil = ⊤ :=
  eq_top_iff.2 fun y _ => etale_bb hε h y

end GlobalTheory.ConstDatum

open GlobalTheory.ConstDatum in

theorem GlobalTheory.PDivLat.hasDatum_of_isConst : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConst G → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  haveI := GlobalTheory.PointGroup.isIntegrallyClosedIn_of_integers hv
  haveI := isLocalRing_of_integers hv
  obtain ⟨hω, hbij⟩ := GlobalTheory.T.constantPDivGroup_omega_trivial_hodgeTate_basis p C v O hv G hG
  haveI := GlobalTheory.PointGroup.finite_tate hv G
  haveI := GlobalTheory.PointGroup.free_tate hv G
  have hrank : Module.finrank ℤ_[p] G.Tate = G.height := G.finrank_tate C
  let e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hrank, Module.finrank_fin_fun])
  let b : Module.Basis (Fin G.height) ℤ_[p] G.Tate := Module.Basis.ofEquivFun e
  let Φ := LinearEquiv.ofBijective _ (hbij G.height b)
  let D := etale ε G.height
  have hF : D.Fil = ⊤ := etale_Fil hε G.height
  let fil : G.dual.omega ≃ₗ[O] D.Fil := Φ.symm ≪≫ₗ (LinearEquiv.ofTop _ hF).symm
  haveI : Subsingleton G.Lie :=
    ⟨fun f g => LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, map_zero]⟩
  haveI : Subsingleton ((Fin G.height → O) ⧸ D.Fil) :=
    ⟨fun a b => by
      obtain ⟨a, rfl⟩ := D.Fil.mkQ_surjective a
      obtain ⟨b, rfl⟩ := D.Fil.mkQ_surjective b
      exact (Submodule.Quotient.eq D.Fil).2 (by rw [hF]; exact Submodule.mem_top)⟩
  refine ⟨D, e, fil, LinearEquiv.ofSubsingleton _ _, fun t => ?_, fun x χ => ?_⟩
  · rw [etale_al]
    change toO e t = ((LinearEquiv.ofTop _ hF).symm (Φ.symm (hodgeTate G t)) : Fin G.height → O)
    rw [LinearEquiv.coe_ofTop_symm_apply, LinearEquiv.eq_symm_apply]
    change Fintype.linearCombination O (fun i => hodgeTate G (b i)) (toO e t) = hodgeTate G t
    rw [Fintype.linearCombination_apply]
    have hb : b.equivFun = e := Module.Basis.equivFun_ofEquivFun e
    conv_rhs => rw [← b.sum_equivFun t]
    rw [map_sum, hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hodgeTate_smul (padicToO p O)]
    rfl
  · rw [Subsingleton.elim x 0]
    simp [pairingO]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.WeilM
open Filter Topology

theorem isLocallyConstant_finprod_evalV {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hcof : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hy : ∀ᶠ v in Filter.cofinite, ∀ i,
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.mono fun v hv => hv
  set T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F)} with hT
  have hTfin : T.Finite := hcof.and hy
  have hO : IsOpen {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hU : ∀ᶠ y' in 𝓝 y, ∀ i, ∀ v, (y' i - y i) v ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i :=
      (continuous_apply i).sub continuous_const
    have hmem : (fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i) y ∈
        {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} := by
      intro v
      simp only [sub_self]
      exact zero_mem _
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)
  have hS : ∀ᶠ y' in 𝓝 y, ∀ v ∈ T, (φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) =
      φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
    refine (Filter.eventually_all_finite hTfin).2 fun v _ => ?_
    have hg : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F =>
        fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    exact ((IsLocallyConstant.iff_eventually_eq _).1 ((hφ v).1.comp_continuous hg)) y
  filter_upwards [hU, hS] with y' hU' hS'
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ T
  · exact hS' v hv
  · have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
        ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      simpa [hT] using hv
    obtain ⟨h1, h2⟩ := hv'
    have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) ∈ v.adicCompletionIntegers F := by
      intro i
      have h4 := add_mem (hU' i v) (h2 i)
      have h5 : (y' i - y i) v + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) := by
        show (y' i) v - (y i) v + (y i) v = (y' i) v
        exact sub_add_cancel _ _
      rwa [h5] at h4
    rw [h1, Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3),
      Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
    rfl

end GlobalTheory.WeilM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj.LocTensor

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem condLE_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {e e' : ℕ} (he : e ≤ e') {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : CondLE ϖ e' χ :=
  fun x hx => h x ⟨hx.1, hx.2.trans (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_right_of_le_one' hϖ.mem he)⟩

theorem isNatDatum_squareFlip [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ C)
    {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {ϖ : kˣ} {e e' : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) (he : e ≤ e') (P : Finset C)
    {Φ : Matrix A' C k → ℂ} (hΦ : IsNatDatum ϖ e' Φ) : IsNatDatum ϖ e' (squareFlip μ σ ψ (α / β) ϖ e' P Φ) := by
  refine (GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A C ψ⁻¹ ϖ e' Pᶜ h.unif h.inv.cond).2 _ ?_
  rw [← latA_blockLat]
  exact GlobalTheory.FrameDepth.hasDepth_phiA k A A' C μ (hμ := hμ) σ _ ϖ e' _ _ h.unif (h.one_le.trans he) (condLE_mono h.unif he h.condν)
    ((GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A' C ψ ϖ e' P h.unif h.cond).1 _ hΦ)

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem isNatDatum_flipAt (hL : L.Is μ₀) (W : G.Weil) {t : T} (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {n : ℕ} (hn : depthAt G w ≤ n)
    {Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ} (hΦ : IsNatDatum (unifAt w) n Φ) :
    IsNatDatum (unifAt w) n (flipAt W t i j w n Φ) := by
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  have := isHaarMeasure_haarVol h2.1 h2.2
  rw [flipAt, ← Grid.alpha_div_beta]
  exact isNatDatum_squareFlip _ _ ((Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2) hn _ hΦ

theorem local_tensors (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) :
    (∃ e, IsIdemSum e (locPl G t)) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeSmall t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.mu t i j) e (ρ.vT i j)) (IsLocVec W (.chi i j) e (ρ.vX i j)) τ Φ) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeBig t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j)) τ Φ) ∧
    ((∀ w ∈ locPl G t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ n Φ, (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        ∃ τ τ', HasFlip B t ρ i j n Φ τ τ' ∧ ∀ b, ∃ a, ρ.Matched a b ∧ IsMatched B t ρ i j (tensT W a τ) (tensT W b τ')) := by
  refine ⟨exists_idemSum_locPl hL G t, fun e he n Φ h => exists_hasLocal_small B ρ t i j hL he h,
    fun e he n Φ h => exists_hasLocal_big B ρ t i j hL he h, fun hb n Φ h => ?_⟩
  obtain ⟨τ, τ', H⟩ := exists_hasFlip_of_nat B ρ t i j hL (fun w hw => (h w hw).2)
    fun w hw => isNatDatum_flipAt hL W i j hw (hb w hw) (h w hw).1 (h w hw).2
  refine ⟨τ, τ', H, fun b => ?_⟩
  obtain ⟨a, ha⟩ := ρ.exists_matched i j b
  exact ⟨a, ha t, a, b, τ, τ', n, Φ, ha t, h, H, rfl, rfl⟩

theorem exists_hasFlip (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (n Φ)
    (h : ∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) :
    ∃ τ τ', HasFlip B t ρ i j n Φ τ τ' ∧ ∀ b, ∃ a, ρ.Matched a b ∧ IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') :=
  (local_tensors hL B ρ t i j).2.2.2 (fun _ hw => Good.badInt_notMem hL hde hc hw) n Φ h

end GlobalTheory.FunObj.LocTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefAndIsBig
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.BirationalBig

theorem isNef_and_isBig : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → IsNef F S.L ∧ IsBig F S.L := by
  intro Q F _ _ S hV hb hB
  have hstr : strHom F S.Y = S.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F S.Y) := hstr ▸ hV.proj
  have hnef : IsNef F S.L := IsGenerated.isNef_of_isProjOver ⟨S.N, S.b, hb⟩ hV.proj
  exact ⟨hnef, (Q.nef.2.2.isBig_iff hproj (GlobalTheory.ImageDegree.topologicalKrullDim_eq S hV) hnef).2
    (GlobalTheory.ImageDegree.degree_image_eq_topSelf Q F S hV hb hB).1⟩

end GlobalTheory.BirationalBig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOfMulEqSmul
section
noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

namespace GlobalTheory.SelfDualFil

theorem isRegular_of_mul_eq_smul {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) : IsRegular M ∧ IsRegular N := by
  have hd : M.det * N.det ≠ 0 := by
    rw [← Matrix.det_mul, H, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact ⟨Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (left_ne_zero_of_mul hd)).1,
    Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (right_ne_zero_of_mul hd)).1⟩

theorem mul_eq_smul_comm {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) :
    N * M = c • (1 : Matrix (Fin h) (Fin h) A) := by
  apply (isRegular_of_mul_eq_smul hc H).1.1
  show M * (N * M) = M * (c • 1)
  rw [← Matrix.mul_assoc, H]
  simp

section

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h : ℕ} {Γ : Type} [CommRing Γ]
  [Algebra ℤ_[p] Γ]

theorem G_eq [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    D.G = D.G.map (phiInv p O) * D.Ψ' := by
  apply (isRegular_of_mul_eq_smul hμ D.G_mul_F).2.2
  show D.G * D.F = D.G.map (phiInv p O) * D.Ψ' * D.F
  have e1 : D.G.map (phiInv p O) * D.F.map (phiInv p O) = nu ε • 1 := by
    rw [← Matrix.map_mul, D.G_mul_F]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, phiInv_mu]
  have e2 : D.Ψ' * D.F = xi ε • D.F.map (phiInv p O) := by
    conv_lhs => rw [D.F_eq]
    rw [← Matrix.mul_assoc, mul_eq_smul_comm hξ D.Ψ_mul]
    simp
  rw [Matrix.mul_assoc, e2, Matrix.mul_smul, e1, smul_smul, xi_mul_nu, D.G_mul_F]

def dualDatum [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    Datum ε h ℤ_[p] where
  F := D.Gᵀ
  G := D.Fᵀ
  Ψ := D.Ψ'ᵀ
  Ψ' := D.Ψᵀ
  ρT := (etale ε h).ρT
  ρM := (etale ε h).ρM
  G_mul_F := by rw [← Matrix.transpose_mul, D.G_mul_F]; simp
  F_eq := by
    rw [Matrix.transpose_map, ← Matrix.transpose_mul, ← G_eq hμ hξ D]
  Ψ_mul := by rw [← Matrix.transpose_mul, D.Ψ_mul]; simp
  F_act := by
    intro a
    have e : ((etale ε h).ρT a).map (ofPadic p O) = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, hij]
    have e' : (etale ε h).ρM a = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Matrix.algebraMap_matrix_apply, hij]
    rw [e, e']
    simp

variable (C : Type) [Field C] [Algebra O C]

end

end GlobalTheory.SelfDualFil
end
end

