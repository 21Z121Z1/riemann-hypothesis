import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0282
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0284
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportCharacters
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidal_support_characters : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  first | (exact @GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (exact GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (intros; apply GlobalTheory.SatSupp.hasSupport_of_hasSatGL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharactersStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidalSupport_twist_nu_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  first | (exact @GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (exact GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (intros; apply GlobalTheory.RoadU.TwistSupp.supp_nu_chars  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ},
  ChIdx.Ok Ch sel mu cst L G m2 → QUnif sel mu → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∀ (g' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z' : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g' z' →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))),
  ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y₁ - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  ((qOf P.1 : X.E) ^ cst.M) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  z' * topDat Ch sel mu cst (m2 + 1) P (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) (g.symm y₁) *
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) =
    z * topDat Ch sel mu cst (m2 + 1) P y y₂ := by
  first | exact @GlobalTheory.TwTopLaw.topLawQ_midTop | exact GlobalTheory.TwTopLaw.topLawQ_midTop | (intros; apply GlobalTheory.TwTopLaw.topLawQ_midTop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K), TopLev Ch sel mu cst j P g z → g ∈ GLint X.E (R.N j) P.1 := by
  first | exact @GlobalTheory.TopLevInt.mem_GLint_of_topLev | exact GlobalTheory.TopLevInt.mem_GLint_of_topLev | (intros; apply GlobalTheory.TopLevInt.mem_GLint_of_topLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SelfTwWeak

theorem trace_of_charpoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (N : Matrix (Fin a) (Fin a) (Qbar l))
    (S : Multiset ℂ) (h : N.charpoly.map ι.toRingHom = (S.map fun b => X - C b).prod) : ι N.trace = S.sum := by
  have h1 := congrArg Polynomial.nextCoeff h
  rw [nextCoeff_map ι.injective, multiset_prod_X_sub_C_nextCoeff] at h1
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, map_neg]
  change -(ι.toRingHom N.charpoly.nextCoeff) = _
  rw [h1, neg_neg]

theorem algSat_mul (n q : ℕ) (B : Multiset ℂˣ) (e : ℂˣ) :
    (UpperTheory.V.Af.algSat n q (B.map (· * e))).sum = (e : ℂ) * (UpperTheory.V.Af.algSat n q B).sum := by
  simp only [UpperTheory.V.Af.algSat]
  simp
  simp only [mul_assoc, Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]
  ring

theorem selfTw_mul_trace_inv (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a)
    (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Weak π ι r) (η : HChar K)
    (hη : UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
      IsPlaceOver A v → IsFrob A (normV v) σ →
        (η.val v : ℂ) * ι (r σ⁻¹).val.trace = ι (r σ⁻¹).val.trace := by
  obtain ⟨-, -, hev⟩ := hr
  filter_upwards [hev, hη] with v hv1 hv2 A σ hA hσ
  obtain ⟨B, hB, hF⟩ := hv1
  obtain ⟨-, B', hB', hBη⟩ := hv2
  have hBB : B' = B := hB'.unique hB
  subst hBB
  have ht := trace_of_charpoly ι _ _ ((hF A hA).2 σ hσ)
  rw [ht]
  conv_rhs => rw [← hBη]
  rw [algSat_mul]

theorem ne_one_of_moves (Ω : Type) [Field Ω] (K : Type) [Field K] [Algebra K Ω] (M : Type) [Field M] [Algebra M Ω]
    [Algebra K M] [IsScalarTower K M Ω] [FiniteDimensional K M] [IsGalois K M] (hp : (Module.finrank K M).Prime)
    (χ : G K Ω →* ℂˣ) (hne : χ ≠ 1)
    (h3 : ∀ g : G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1) (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : χ g ≠ 1 := by
  classical
  let ρ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hfix : ∀ k : G K Ω, ρ k = 1 → ∀ x : M, k (algebraMap M Ω x) = algebraMap M Ω x := by
    intro k hk x
    have := AlgEquiv.restrictNormal_commutes k M x
    rw [← this]
    change algebraMap M Ω (ρ k x) = _
    rw [hk]; rfl
  haveI : Fact (Nat.card (M ≃ₐ[K] M)).Prime := ⟨by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hp)
      | (convert hp using 1; rw [Nat.card_eq_fintype_card]; convert IsGalois.card_aut_eq_finrank K M)⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((χ.ker).map ρ) with hH | hH
  · intro hχg
    obtain ⟨x, hx⟩ := hg
    have : ρ g ∈ (χ.ker).map ρ := ⟨g, hχg, rfl⟩
    rw [hH, Subgroup.mem_bot] at this
    exact hx (hfix g this x)
  · exfalso
    apply hne
    ext k
    have : ρ k ∈ (χ.ker).map ρ := by rw [hH]; trivial
    obtain ⟨k', hk', hkk⟩ := this
    have h1 : χ (k * k'⁻¹) = 1 := h3 _ (hfix _ (by rw [map_mul, map_inv, hkk, mul_inv_cancel]))
    rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk', inv_one, mul_one] at h1
    simp [h1]

theorem inv_moves {Ω K M : Type} [Field Ω] [Field K] [Algebra K Ω] [Field M] [Algebra M Ω] (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : ∃ x : M, g⁻¹ (algebraMap M Ω x) ≠ algebraMap M Ω x := by
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, fun h => hx ?_⟩
  have e : (g * g⁻¹) (algebraMap M Ω x) = algebraMap M Ω x := by rw [mul_inv_cancel]; rfl
  rw [AlgEquiv.mul_apply, h] at e
  exact e

theorem trace_eq_zero_of_selfTw : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] [IsGalois K M], (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ η : HChar K, UpperTheory.V.Published.IsNormChar M η → UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η → ∀ g : G K Ω, (∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) → (r g).val.trace = 0 := by
  intro Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ _ hp l _ ι a π r hr η hη hst g hg
  obtain ⟨χ, hχo, hχ1, hχf⟩ :=
    GlobalTheory.HeckeToGal.exists_galChar_of_finite_order Ω K η (Module.finrank K M) hp.pos hη.2.1
  have hχne : χ ≠ 1 := fun h => hη.1 (hχ1 h)
  have h3 := GlobalTheory.trivial_on_ext_of_frob_eq_normChar Ω K M η hη χ hχo hχf
  have hne := ne_one_of_moves Ω K M hp χ hχne h3 g⁻¹ (inv_moves g hg)
  have h1 := selfTw_mul_trace_inv Ω K l ι a π r hr η hst
  have hcont : Continuous r := hr.1
  have hUo : IsOpen {k : G K Ω | χ k ≠ 1} := by
    have hc : IsClosed (χ.ker : Set (G K Ω)) := Subgroup.isClosed_of_isOpen _ hχo
    have : {k : G K Ω | χ k ≠ 1} = (χ.ker : Set (G K Ω))ᶜ := by ext k; simp [MonoidHom.mem_ker]
    rw [this]; exact hc.isOpen_compl
  have hT := Filter.eventually_cofinite.1 (h1.and hχf)
  have hD := GlobalTheory.frob_dense_off_finite K Ω _ hT
  have hc : Continuous fun k : G K Ω => (r k⁻¹).val.trace :=
    (Units.continuous_val.comp (hcont.comp continuous_inv)).matrix_trace
  have hZ : IsClosed {k : G K Ω | (r k⁻¹).val.trace = 0} := isClosed_eq hc continuous_const
  have hsub := hD.open_subset_closure_inter hUo hne
  have key : (r g⁻¹⁻¹).val.trace = 0 := by
    refine closure_minimal ?_ hZ hsub
    rintro σ ⟨hσU, v, hv, A, hA, hσ⟩
    simp only [Set.mem_setOf_eq, not_not] at hv
    have e1 := hv.1 A σ hA hσ
    have e2 := hv.2 A σ hA hσ
    have hv1 : (η.val v : ℂ) ≠ 1 := by
      intro h; apply hσU; rw [e2]; exact Units.val_eq_one.1 h
    have : ι (r σ⁻¹).val.trace = 0 := by
      have h0 : ((η.val v : ℂ) - 1) * ι (r σ⁻¹).val.trace = 0 := by rw [sub_mul, e1, one_mul, sub_self]
      exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hv1)
    exact (map_eq_zero_iff ι ι.injective).1 this
  rwa [inv_inv] at key

end GlobalTheory.SelfTwWeak

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardBaseLevelPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pdv

theorem stabStd_eq_stabSet {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun γ => (fun v => γ.1 v) '' ((I.stp u a i).rep c).1.2 = ((I.stp u a i).rep c).1.2) := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hs : _ = _ := s.2
    refine ⟨s.1, congrArg (fun p => p.1.1) hs, congrArg (fun p => p.1.2) hs, ?_⟩
    refine Prod.ext ?_ rfl
    exact GlobalTheory.KerJ.ufGL_val s.1.1
  · rintro ⟨b, hb, hq, rfl⟩
    refine ⟨⟨b, Subtype.ext (Prod.ext hb hq)⟩, ?_⟩
    refine Prod.ext ?_ rfl
    exact (GlobalTheory.KerJ.ufGL_val b.1).symm

theorem rep_coset_empty {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m)
    (c : (I.stp u a i).Cl) : ((I.stp u a i).rep c).1.2 = ∅ := by
  have key : ∀ y : Ys B.fields (B.R.N i), y = Ys.triv _ _ → ∀ s N, s ∈ y.ys N → s = ∅ := by
    rintro y rfl s N hs
    exact hs
  exact key _ (by unfold ysAt; exact if_neg hi) _ _ ((I.stp u a i).rep c).2

theorem stabStd_eq_stabSet_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun _ => True) := by
  rw [stabStd_eq_stabSet, rep_coset_empty I u a i hi c]
  congr 1
  funext γ
  simp

theorem stab_pin : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → ∀ u a, GlobalTheory.KerJ.StabPin t u a (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I hI hP l Z L hT Gi Gl K Y cX ex t hN hK hR u a
  change B.Word at u
  change I.ι at a
  obtain ⟨cc, cc_rec, cc_ok, δ', δ_ok, B', χ, χ_ok, idl, idl_ok, χ_rec, cD, X', seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S', word,
    T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf,
    kf_un, served⟩ := t
  obtain ⟨hX, hseam, hPr, hCh, hsel, hS, hword, htup, hcst, hidx, hm2, -, -, -, -⟩ := hK
  subst hX
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hCh
  obtain rfl := eq_of_heq hsel
  subst hS
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hidx
  subst hm2
  obtain ⟨r, hr, hrs⟩ := hR u a
  obtain rfl := eq_of_heq hr
  unfold GlobalTheory.KerJ.StabPin
  dsimp only
  have hm : B.R.m = B.R.m - 2 + 2 := (hI.idx_ok a).hm
  have h1 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  obtain ⟨hXo, hPro, -⟩ := base_fields_primes_ok B X
  have hG : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get h) := by
    intro j b h
    unfold levGAt
    rw [← Idx.some_get b h]
    rfl
  have hQ : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levQ j (b.get h) := by
    intro j b h
    unfold levQAt
    rw [← Idx.some_get b h]
    rfl
  have hGt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twLt I.Ch B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levGAt
    rw [hb]
    exact (topLev_levG_m _ _ _ _ _).trans (GlobalTheory.T.typePrimeLevel_lastStep_symmetricRows_eq_twistLevel B.fields (B.primes X) B.R I.Ch hXo hPro hI.ch_ok)
  have hQt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twTt (R := B.R) I.sel (I.tup a) B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levQAt
    rw [hb]
    refine (topLev_levQ_m _ _ _ _ _).trans ?_
    have hd : topDep B.R (I.cst a).M = 4 * B.R.m := by
      have := (hN a).2.1
      unfold topDep
      exact max_eq_left (by omega)
    rw [hd]
    exact GlobalTheory.T.level_quotient_eq_twisted_top B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) hXo hPro hI.sel_ok (fun i => hI.g_mem i)
      (fun v => hI.T_mem v)
  have hTop : ∀ j (hj : j = B.R.m) (c : ((I.rec7 l Z).chTw u a).cls j),
      stabStd I l Z u a j c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (twLt I.Ch j)
        (twTt (R := B.R) I.sel (I.tup a) j) ((I.stp u a j).rep c).1.1 (fun _ => True) := by
    intro j hj c
    subst hj
    rw [stabStd_eq_stabSet_triv I l Z u a _ (by omega) c, hGt, hQt]
  refine ⟨fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => c.1.get (by omega),
    fun c => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2, fun c => ((I.stp u a (B.R.m - 2 + 1 + 1)).rep c).1.1,
    fun i _ c => hrs.1 i c, fun c => PtAt.mem_ybSet _ h1, ?_, ?_, ⟨fun c' => hrs.1 _ c', ?_⟩, ?_, ?_, fun c => hTop _ h1 c⟩
  · intro i hi c c' x
    rw [hrs.2 i (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm
      (Idx.some_get c'.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) h1,
      GlobalTheory.T.lastColumnStepDatum_eq_twistTopDatum B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) u (B.R.m - 2) h1]
    rfl
  · intro i _ hi c
    rw [stabStd_eq_stabSet_triv I l Z u a i (by omega) c, hG i c.1 (by omega), hQ i c.1 (by omega)]
    rfl
  · intro b c
    obtain ⟨b0, hb0⟩ := (hI.idx_ok a).last_uniq
    have hcb : c.1.get (by omega) = b := (hb0 _).trans (hb0 b).symm
    rw [stabStd_eq_stabSet, hG _ c.1 (by omega), hQ _ c.1 (by omega), hcb]
    rfl

end GlobalTheory.Pdv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnOrthonormalCoordsEqGivenStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_orthonormalCoords_eq_given : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY Kc)), I.StdKer l Z t → (∀ i hi, I.IdY l Z u a i hi (eY i hi)) → AdPins A dt → ∀ i hi, A.crd i hi = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.crd_eq_one | exact GlobalTheory.TwU.AtTrue.crd_eq_one | (intros; apply GlobalTheory.TwU.AtTrue.crd_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmoothStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N (i + 1)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true | exact GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true | (intros; apply GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixing
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem unram_comp_normU_of_fix : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  intro Ω _ E _ _ _ _ M _ _ _ _ _ _ A w u h h' _ n ξ a ha H j x hx
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  have h1 : ValuativeRel.valuation (u.adicCompletion M) (x : u.adicCompletion M) = 1 := by
    have : (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion M))
      (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.2 hx
  obtain ⟨τ, rfl⟩ := ha'.surj x
  have hdeg : deg τ = 0 := by
    have := ha'.ord_eq τ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at this
    omega
  obtain ⟨t, ht, hd⟩ := GlobalTheory.AboveL.exists_weil_restrict E M Ω A w u h h' τ
  rw [← GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' t τ ht]
  exact H t (hd.2 hdeg) (fun y => by rw [ht]; exact AlgEquiv.commutes _ y) j

end GlobalTheory.RoadU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobeniusStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  first | (exact @GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (exact GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (intros; apply GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig  <;> assumption)
end

