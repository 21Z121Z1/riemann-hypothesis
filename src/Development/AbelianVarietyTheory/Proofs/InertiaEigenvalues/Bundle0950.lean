import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0946
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0133
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjCoverFunctionEqConstMulConjTuple
section
noncomputable section

namespace GlobalTheory.CoverConj

section General

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.GalTw
  GlobalTheory.GalTw.CharSec
open scoped TensorProduct Matrix

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_conj_pt_fix (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ) (hτ : ∀ a, τ (σ a) = σ a) (y : FrPt Xo c (CAt σ)) :
    ∃ y₀ : FrPt Xo c (CAt σ), ∀ f ∈ sec Xo c 0 0, toC (evR Xo c f y) = τ (toC (evR Xo c f y₀)) := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  let φ : CAt σ →ₐ[c.F] CAt σ :=
    { toRingHom := (τ.symm : ℂ →+* ℂ)
      commutes' := fun a => by
        show τ.symm (σ a) = σ a
        conv_lhs => rw [← hτ a]
        exact τ.symm_apply_apply _ }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS D.host.E H Dw l Xo c _ _ φ y
  have hx : y.x = spMap (τ : ℂ →+* ℂ) ≫ z.x := by
    have h1 : z.x = spMap (τ.symm : ℂ →+* ℂ) ≫ y.x := hz.1
    have h2 : spMap (τ : ℂ →+* ℂ) ≫ spMap (τ.symm : ℂ →+* ℂ) = 𝟙 _ := by
      unfold spMap
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      simp
    rw [h1]
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) h2).trans (Category.id_comp _))).symm
  exact ⟨z, fun f hf => conj_value σ σ τ (RingHom.ext fun a => (hτ a).symm) hf z y hx⟩

set_option maxHeartbeats 2000000 in

theorem galRul_eq_cmul_complex (V : HSp D) (r : ℕ) (σ : c.F →+* ℂ) (C : Ctx Xo c σ V r) (hC : C.OK)
    (hsig : Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) {ta : c.F ≃+* c.F} (hta : Fixes c ta) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a, τ (σ a) = σ (ta a)) (hcur : FixesCurve H τ 1) (xi xi' : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hx1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1)
    (hx2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1)
    (hconj : ∀ h : GA D V, τ (xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ) =
      (xi' (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ))
    (a₀ a₀' : ℂ) (ha' : a₀' ≠ 0) {f f' : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (hf' : f' ∈ sec Xo c 0 0)
    (hv : ∀ (y : FrPt Xo c (CAt σ)) k P, IsPeriod (C.F.Di k) (fun j => relab c σ (C.e j).1) P → y.x = C.F.u k P →
      ∀ h γ, C.Mark h k γ → toC (evR Xo c f y) = a₀ * (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ))
    (hv' : ∀ (y : FrPt Xo c (CAt σ)) k P, IsPeriod (C.F.Di k) (fun j => relab c σ (C.e j).1) P → y.x = C.F.u k P →
      ∀ h γ, C.Mark h k γ → toC (evR Xo c f' y) = a₀' * (xi' (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ)) :
    ∃ (u : GA D V) (ka : c.F), σ ka = τ a₀ / a₀' * ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ)⁻¹ ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k),
        evR Xo c (galRul hta f) y = algebraMap c.F k ka * evR Xo c f' y := by
  haveI : Countable c.F := (Module.finBasis ℚ c.F).equivFun.toEquiv.countable_iff.2 inferInstance
  have hg : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hC.good
  have hrt : τ H.rt0 = H.rt0 := by
    conv_lhs => rw [← hg, hτ, hta.base, hg]
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_perm_periodSpaces_complexAut D.host.E H Dw l Xo _ _ _ C.F hC.pos hC.good
    ((GlobalTheory.Relab.relab_good D.host.E H l c σ hC.good).2.2.2 Dw C.g C.e) hC.lA τ hrt
  obtain ⟨κ, ⟨u, hu⟩, hκ⟩ := GlobalTheory.T.autConj_translates_detCharacter_markings D H Dw l Xo c σ V r C hC hsig τ hrt hcur π hπ xi hx1 hx2
  have hcu := hconj u
  rw [← hu] at hcu
  have hgal : galRul hta f ∈ sec Xo c 0 0 := ((GlobalTheory.T.conjugateSection_values_semilinear D.host.E H Dw l Xo c ta hta).1 0 0 f hf).1
  have hne : ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hpt : ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c (galRul hta f) y) =
      (τ a₀ / a₀' * ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ)⁻¹) * toC (evR Xo c f' y) ∧
      toC (evR Xo c f' y) ≠ 0 := by
    intro y
    obtain ⟨y₀, hy, hval⟩ := exists_conj_point σ hta τ hτ y
    obtain ⟨i, P, hP, hiP⟩ := C.F.onto y₀.x y₀.x_over
    obtain ⟨P', hP', hiP'⟩ := hπ i P hP
    obtain ⟨h, -, hm⟩ := GlobalTheory.Member.exists_finite_mark D H Dw l Xo c σ V r C hC i
    obtain ⟨h', -, hm'⟩ := GlobalTheory.Member.exists_finite_mark D H Dw l Xo c σ V r C hC (π i)
    have e1 := hv y₀ i P hP hiP.symm h 1 hm
    have e2 := hv' y (π i) P' hP' (hy.trans (hiP ▸ hiP')) h' 1 hm'
    have e3 := hκ h 1 i h' 1 hm hm'
    have e4 := hval f hf
    refine ⟨?_, ?_⟩
    · rw [e4, e1, e2, ← hconj (1 * h'), e3, Units.val_mul, map_mul τ, map_mul τ, hcu]
      field_simp
    · rw [e2]
      exact mul_ne_zero ha' (Units.ne_zero _)
  obtain ⟨y1⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ _ _
    Xo c hC.pos σ
  have hmem : (τ a₀ / a₀' * ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ)⁻¹) ∈ Set.range σ := by
    letI : Algebra c.F ℂ := σ.toAlgebra
    refine GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := c.F) _ fun s => ?_
    have hs : ∀ a, s.toRingEquiv (σ a) = σ a := fun a => s.commutes a
    obtain ⟨y₀, hy₀⟩ := exists_conj_pt_fix σ s.toRingEquiv hs y1
    have h1 := (hpt y1).1
    have hn := (hpt y1).2
    rw [hy₀ _ hgal, hy₀ _ hf', (hpt y₀).1, map_mul] at h1
    rw [hy₀ _ hf'] at hn
    exact mul_right_cancel₀ hn h1
  obtain ⟨ka, hka⟩ := hmem
  refine ⟨u, ka, hka, ?_⟩
  have hsplit : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (t : c.F),
      evR Xo c (galRul hta f + (-t) • f') y = evR Xo c (galRul hta f) y - algebraMap c.F S t * evR Xo c f' y := by
    intro S _ _ y t
    unfold evR
    rw [evalAt_add, evalAt_smul, map_neg, neg_mul, sub_eq_add_neg]
  have hz : galRul hta f + (-ka) • f' = 0 := by
    refine sec_eq_zero_of_complex σ (add_mem hgal (Submodule.smul_mem _ _ hf')) fun y => ?_
    rw [hsplit, sub_eq_zero]
    show toC (evR Xo c (galRul hta f) y) = σ ka * toC (evR Xo c f' y)
    rw [hka]
    exact (hpt y).1
  intro k _ _ _ y
  have e := hsplit k y ka
  rw [hz] at e
  have e0 : evR Xo c (0 : Rul Xo c) y = 0 := evalAt_zero _ _ y
  exact sub_eq_zero.1 (e.symm.trans e0)

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

section Transport

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
  {c : Coeff l}

theorem cxiAt_of_eq (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {d d' : DeltaDat Xo c n} (e : d' = d)
    {U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r}
    {U₂' : Unf d'.Xo₂ d'.c₂ (σ0.comp (d'.eF.symm : d'.c₂.F →+* c.F)) r} (hU : HEq U₂' U₂)
    {dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r} {dict₂' : GA D V → Σ k, Frame (U₂'.X k).Ψ r} (hd : HEq dict₂' dict₂)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ)
    (h : GlobalTheory.OneMapAll.CXiAt V hr σ0 d' U₂' dict₂' ι x₀ xi c0) : GlobalTheory.OneMapAll.CXiAt V hr σ0 d U₂ dict₂ ι x₀ xi c0 := by
  subst e
  obtain rfl := eq_of_heq hU
  obtain rfl := eq_of_heq hd
  exact h

theorem cδ_mem_of_eq {d d' : DeltaDat Xo c n} (e : d' = d) (h : d'.cδ ∈ sec d'.Xo₂ d'.c₂ 0 0) :
    d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 := e ▸ h

end Transport

set_option maxHeartbeats 4000000 in

theorem conj_cover_const : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ k0 : ℂ, IsRoot1 k0 ∧ ∀ (a b : Tp) (cx : Rul (M.dδ a).Xo₂ (M.dδ a).c₂), M.dδ b = { M.dδ a with cδ := cx } → HEq (M.U₂ b) (M.U₂ a) → HEq (M.dict₂ b) (M.dict₂ a) → ConjTup R τ (tup a) (tup b) → ∃ (h₂ : Fixes (M.dδ a).c₂ (covAut (M.dδ a) ta)) (ka : M.c'.F) (s : (AE D)ˣ), (ka : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ a).c₂.F k] (y₂ : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ k), evR (M.dδ a).Xo₂ (M.dδ a).c₂ (galRul h₂ (M.dδ a).cδ) y₂ = algebraMap (M.dδ a).c₂.F k ((M.dδ a).eF ka) * evR (M.dδ a).Xo₂ (M.dδ a).c₂ cx y₂ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup M hM τ ta hta hFix hcO hxiF
  obtain ⟨c0, ⟨m, hm0, hm⟩, hc⟩ := (GlobalTheory.OneMapAll.cXiVal_iff _ _ _ _ _ _ _ _ _).1 hM.cxi
  have hc0 : c0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne'] at hm
    exact zero_ne_one hm
  refine ⟨τ c0 / c0, ⟨m, hm0, by rw [div_pow, ← map_pow, hm, map_one, div_one]⟩, ?_⟩
  intro a b cx hab hU hd hct
  have hfix' : Fixes M.c' ta := by
    refine ⟨fun τ' x => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · rw [hta]
      exact hFix.host τ' x
    · rw [hta]
      exact hFix.core ⟨_, T.Q.c.le x.2⟩
  obtain ⟨hlev, hA, -⟩ := hM.cov a
  have h₂ := fixes_covAut (M.dδ a) hA hfix'
  refine ⟨h₂, ?_⟩
  obtain ⟨hT'⟩ := hT
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  obtain ⟨-, hpq, -, hq2⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT'.laws.pins ((i : ℕ) + 1) hj
  have hsig : (T.Q.Dw ((i : ℕ) + 1)).p = 0 ∨ (T.Q.Dw ((i : ℕ) + 1)).q = 0 ∨
      3 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    by_cases h0 : (T.Q.Dw ((i : ℕ) + 1)).q = 0
    · exact Or.inr (Or.inl h0)
    · right; right; omega
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hιok := GlobalTheory.TupleCover.iotaOK_and_frame T hT'.laws ((i : ℕ) + 1) hj M.s0
    (by have e : M.s0 = T.σ₀ := sOv_eq _ _ _; rw [e]; exact T.good_σ₀) (Wc D i) M.hV (rank_Wc i)
  let σ₂ : (M.dδ a).c₂.F →+* ℂ := (inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)
  obtain ⟨C, hC, hCι, hCx⟩ := (GlobalTheory.Member.exists_ctx D _ _ _ (M.dδ a).Xo₂ (M.dδ a).c₂ σ₂ (Wc D i) D.R.r (rank_Wc i) _
    hιok.1 hpos hA rfl).2.2 _ hιok.2
  have hτ₂ : ∀ x, τ (σ₂ x) = σ₂ (covAut (M.dδ a) ta x) := fun x => by
    show τ (((M.dδ a).eF.symm x : M.c'.F) : ℂ) =
      (((M.dδ a).eF.symm ((M.dδ a).eF (ta ((M.dδ a).eF.symm x))) : M.c'.F) : ℂ)
    rw [AlgEquiv.symm_apply_apply, hta]
  have hconj : ∀ h : GA D (Wc D i), τ ((M.xi a (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) : ℂˣ) : ℂ) =
      ((M.xi b (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) : ℂˣ) : ℂ) := fun h => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 h
    rw [(hM.tuple a).xi h x hx, (hM.tuple b).xi h x hx, hct.2 x]
  have hrat : ∀ t : Tp, ∀ γ ∈ GQ (Wc D i), M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1 := by
    intro t γ hγ
    obtain ⟨-, -, hr3, -⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
    obtain ⟨x, hx⟩ := hr3 γ hγ
    apply Units.ext
    rw [(hM.tuple t).xi γ _ hx, (hR.lev.xi (tup t)).1.2 x]
    simp
  have hl₂ : (M.dδ b).l₂ = (M.dδ a).l₂ := by rw [hab]
  have hxa := GlobalTheory.T.coverCharacter_trivial_on_level_determinants D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM a
  have hxb : ∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F
      (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) :
        (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) →
      M.xi b (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
    intro u hu hw
    rw [← hl₂] at hw
    exact GlobalTheory.T.coverCharacter_trivial_on_level_determinants D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM b u hu hw
  have hfa : (M.dδ a).cδ ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 := hlev.2.2.2.2.2.2.2.1
  have hfb : cx ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 :=
    cδ_mem_of_eq (d := { M.dδ a with cδ := cx }) hab (hM.cov b).1.2.2.2.2.2.2.2.1
  have hva := GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM a C hC hCι hCx (M.dδ a).cδ (M.xi a) c0
    hfa hxa (hrat a) (hc a)
  have hvb := GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM a C hC hCι hCx cx (M.xi b) c0
    hfb hxb (hrat b) (cxiAt_of_eq _ _ _ (d := { M.dδ a with cδ := cx }) hab hU hd _ _ _ _ (hc b))
  obtain ⟨u, ka₂, hka, heq⟩ := galRul_eq_cmul_complex (Wc D i) D.R.r σ₂ C hC hsig h₂ τ hτ₂ hFix.curve (M.xi a) (M.xi b)
    hxa (hrat a) hconj c0 c0 hc0 hfa hfb hva hvb
  obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 u
  refine ⟨(M.dδ a).eF.symm ka₂, x⁻¹, ?_, fun k _ _ _ y => ?_⟩
  · show σ₂ ka₂ = _
    rw [hka, (hM.tuple b).xi u x hx, map_inv, Circle.coe_inv]
  · rw [AlgEquiv.apply_symm_apply]
    exact heq k y

end GlobalTheory.CoverConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparable
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial

namespace GlobalTheory.JR.DenseMatch

theorem charpoly_companion {k : Type} [CommRing k] :
    ∀ (r : ℕ) (p : Fin r → k), (companion p).charpoly = X ^ r + ∑ i : Fin r, C (p i) * X ^ (i : ℕ) := by
  intro r
  induction r with
  | zero => intro p; simp [Matrix.charpoly, Matrix.det_isEmpty]
  | succ s ih =>
    cases s with
    | zero =>
      intro p
      simp [Matrix.charpoly, Matrix.det_unique, charmatrix_apply, companion]
    | succ n =>
      intro p
      have h00 : (charmatrix (companion p)).submatrix Fin.succ Fin.succ
          = charmatrix (companion (fun i : Fin (n + 1) => p i.succ)) := by
        ext i j
        simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply, Fin.succ_inj,
          Fin.val_succ]
        split_ifs <;> first | rfl | simp_all | omega
      have hlast : ((charmatrix (companion p)).submatrix Fin.succ (Fin.last (n + 1)).succAbove).det
          = (-1) ^ (n + 1) := by
        rw [Fin.succAbove_last, Matrix.det_of_upperTriangular]
        · have : ∀ i : Fin (n + 1), (charmatrix (companion p)).submatrix Fin.succ Fin.castSucc i i = -1 := by
            intro i
            simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply]
            split_ifs <;> simp_all [Fin.ext_iff] <;> omega
          simp only [submatrix_apply] at this
          simp [this]
        · intro i j hij
          simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply]
          have : (j : ℕ) < i := hij
          split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      rw [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
        Finset.sum_eq_single (Fin.last n)]
      · rw [Fin.succAbove_zero, h00, ← Matrix.charpoly, ih, Fin.succ_last, hlast]
        have e1 : charmatrix (companion p) 0 0 = X := by
          simp [charmatrix_apply, companion]
        have e2 : charmatrix (companion p) 0 (Fin.last (n + 1)) = C (p 0) := by
          simp [charmatrix_apply, companion, Fin.ext_iff]
        rw [e1, e2, Fin.sum_univ_succ (n := n + 1)]
        simp only [Fin.val_last, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
        have : ((-1 : k[X]) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
        have e3 : ∑ x : Fin (n + 1), C (p x.succ) * X ^ ((x : ℕ) + 1)
            = X * ∑ i : Fin (n + 1), C (p i.succ) * X ^ (i : ℕ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
        rw [e3, Nat.succ_eq_add_one]
        linear_combination C (p 0) * this
      · intro j _ hj
        have : charmatrix (companion p) 0 j.succ = 0 := by
          have hjn : (j : ℕ) ≠ n := fun h => hj (Fin.ext (by simp [h]))
          rw [charmatrix_apply, diagonal_apply_ne _ (Fin.succ_ne_zero j).symm]
          simp only [companion, of_apply, Fin.val_succ, Fin.val_zero]
          rw [if_neg (by omega)]
          simp
        rw [this, mul_zero, zero_mul]
      · simp

end GlobalTheory.JR.DenseMatch

namespace GlobalTheory.JR.DenseMatch

theorem finite_not_separable_add_C {F : Type} [Field F] [CharZero F] (P : F[X]) :
    {t : F | ¬ (P + C t).Separable}.Finite := by
  by_cases hd : derivative P = 0
  · obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨P.coeff 0, eq_C_of_derivative_eq_zero hd⟩
    refine (Set.finite_singleton (-c)).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, ← C_add, separable_C, isUnit_iff_ne_zero, not_not] at ht
    simp only [Set.mem_singleton_iff]; linear_combination ht
  · let K := AlgebraicClosure F
    have hfin : ((fun α : K => -aeval α P) '' (derivative P).rootSet K).Finite :=
      ((derivative P).rootSet_finite K).image _
    refine (hfin.preimage (algebraMap F K).injective.injOn).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K,
      not_forall, not_or, not_not, derivative_add, derivative_C, add_zero] at ht
    obtain ⟨α, h1, h2⟩ := ht
    refine ⟨α, ?_, ?_⟩
    · rw [mem_rootSet]; exact ⟨hd, h2⟩
    · simp only [map_add, aeval_C] at h1
      linear_combination -h1

theorem frequently_of_curve {Y F : Type} [TopologicalSpace Y] [NontriviallyNormedField F] (γ : F → Y)
    (hγ : Continuous γ) (x₀ : Y) (h0 : γ 0 = x₀) (P : Y → Prop) (hfin : {t | ¬ P (γ t)}.Finite) :
    ∃ᶠ x in 𝓝 x₀, P x := by
  intro hne
  have h1 : ∀ᶠ t in 𝓝[≠] (0 : F), ¬ P (γ t) :=
    ((h0 ▸ hγ.tendsto 0).mono_left nhdsWithin_le_nhds).eventually hne
  have h2 : ∀ᶠ t in 𝓝[≠] (0 : F), t ∉ {t | ¬ P (γ t)} := by
    have hc : IsClosed ({t | ¬ P (γ t)} \ {0}) := (hfin.subset Set.diff_subset).isClosed
    have : ∀ᶠ t in 𝓝 (0 : F), t ∉ ({t | ¬ P (γ t)} \ {0}) := hc.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with t ht ht0
    exact fun hb => ht ⟨hb, ht0⟩
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact ht2 ht1

theorem continuous_Delta {r : ℕ} {F : Type} [NontriviallyNormedField F] :
    Continuous (fun a : Inv r F => Delta a) := by
  have hc : Continuous (fun p : Fin r → F => companion p) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [companion, of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const
  have hc' : Continuous (fun a : Inv r F => companion a.1) := hc.comp continuous_fst
  unfold Delta
  apply Continuous.matrix_det
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [hankel, of_apply, mom, sec]
  exact (continuous_snd.fst).dotProduct ((hc'.pow _).matrix_mulVec continuous_const)

end GlobalTheory.JR.DenseMatch

namespace GlobalTheory.JR.DenseMatch

theorem frequently_separable {F : Type} [NontriviallyNormedField F] [CharZero F] :
    ∀ (r : ℕ) (a₀ : Inv r F), ∃ᶠ a in 𝓝 a₀, (companion a.1).charpoly.Separable
  | 0, a₀ => (Eventually.of_forall fun a => by rw [charpoly_companion]; simp).frequently
  | s + 1, a₀ => by
    have key : ∀ t : F, (companion (a₀.1 + Pi.single 0 t)).charpoly = (companion a₀.1).charpoly + C t := by
      intro t
      rw [charpoly_companion, charpoly_companion, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp [Pi.single_apply, Fin.succ_ne_zero]
      ring
    have hs : Continuous (fun t : F => (Pi.single 0 t : Fin (s + 1) → F)) :=
      continuous_pi fun i => by simp only [Pi.single_apply]; split_ifs <;> fun_prop
    refine frequently_of_curve (fun t : F => ((a₀.1 + Pi.single 0 t, a₀.2) : Inv (s + 1) F)) (by fun_prop) a₀
      (by simp) (fun a => (companion a.1).charpoly.Separable) ?_
    refine (finite_not_separable_add_C (companion a₀.1).charpoly).subset fun t ht => ?_
    simpa [key] using ht

theorem frequently_mom_ne_zero {F : Type} [NontriviallyNormedField F] (s : ℕ) (a₀ : Inv (s + 1) F) :
    ∃ᶠ a in 𝓝 a₀, mom (sec a) 0 ≠ 0 := by
  have key : ∀ a : Inv (s + 1) F, mom (sec a) 0 = a.2.1 0 := by
    intro a; simp [mom, sec, dotProduct, Fin.sum_univ_succ, Fin.succ_ne_zero]
  have hs : Continuous (fun t : F => (Pi.single 0 t : Fin (s + 1) → F)) :=
    continuous_pi fun i => by simp only [Pi.single_apply]; split_ifs <;> fun_prop
  refine frequently_of_curve (fun t : F => ((a₀.1, a₀.2.1 + Pi.single 0 t, a₀.2.2) : Inv (s + 1) F))
    (by fun_prop) a₀ (by simp) (fun a => mom (sec a) 0 ≠ 0) ?_
  refine (Set.finite_singleton (-a₀.2.1 0)).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq, key, not_not, Pi.add_apply, Pi.single_eq_same] at ht
  simp only [Set.mem_singleton_iff]; linear_combination ht

theorem match_of_frequently {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (G : Inv r F → Prop) (hG : ∀ a₀ : Inv r F, ∃ᶠ a in 𝓝 a₀, G a)
    (h : ∀ a : Inv r F, Delta a ≠ 0 → G a → MatchAt M f' f a) : Match M f' f := by
  intro a₀ hΔ
  have hcont : ∀ᶠ a in 𝓝 a₀, Delta a ≠ 0 := continuous_Delta.continuousAt.eventually_ne hΔ
  have hL7 := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M
  have hO := hL7.2.2.1 f' hf' a₀ hΔ
  constructor
  · intro X hX
    have hU := hL7.2.2.2 f hf a₀ X hΔ hX
    obtain ⟨a, ha1, ha2, ha3, ⟨X', hX'⟩, hUX⟩ := ((hG a₀).and_eventually (hcont.and (hO.and hU))).exists
    rw [← ha3, (h a ha2 ha1).1 X' hX', hUX X' hX']
  · intro hno
    have h5 := (GlobalTheory.T.invariant_image_openClosed_local_sections F E r a₀ hΔ).1 hno
    obtain ⟨a, ha1, ha2, ha3, ha4⟩ := ((hG a₀).and_eventually (hcont.and (hO.and h5))).exists
    rw [← ha3]
    exact (h a ha2 ha1).2 ha4

theorem match_of_dense : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ),
    IsTest f' → IsTest f →
      ((∀ a : Inv r F, Delta a ≠ 0 → (companion a.1).charpoly.Separable → MatchAt M f' f a) → Match M f' f) ∧
      (0 < r → (∀ a : Inv r F, Delta a ≠ 0 → mom (sec a) 0 ≠ 0 → MatchAt M f' f a) → Match M f' f) := by
  intro F E _ _ _ _ _ r M f' f hf' hf
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  refine ⟨fun h => match_of_frequently M f' f hf' hf _ (frequently_separable r) h, fun hr h => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
  exact match_of_frequently M f' f hf' hf _ (frequently_mom_ne_zero s) h

end GlobalTheory.JR.DenseMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExpone
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.RamShift

theorem condOne_condExp : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  intro E _ _ ϖ w hϖ
  obtain ⟨ψ, hψ, hlc, hne⟩ := GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one E w
  have hcont : Continuous ψ := hlc.continuous
  have hnorm : ∀ t, ‖ψ t‖ = 1 := fun t => by
    rw [hψ]; exact Circle.norm_coe _
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent E w ψ hcont hnorm hne'
  have hval : Valued.v (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = WithZero.exp n := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    rw [← WithZero.exp, ← WithZero.exp_zsmul]
    simp
  have key : CondOne w (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
    intro x
    have h1 := hn ((((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) * x)
    simp only [hψ] at h1
    rw [map_mul, hval] at h1
    have h2 : WithZero.exp n * Valued.v x ≤ WithZero.exp n ↔ Valued.v x ≤ 1 := by
      conv_lhs => rhs; rw [← mul_one (WithZero.exp n)]
      exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)
    rw [h2] at h1
    exact h1
  unfold condExp
  split_ifs with h1 h2
  · simpa using h1
  · exact h2.choose_spec
  · exact absurd ⟨-n, key⟩ h2

end GlobalTheory.RamShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarAndSizeBoundStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_and_size_bound : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  first | exact @GlobalTheory.NLink.rowsAD_in_setting | exact GlobalTheory.NLink.rowsAD_in_setting | (intros; apply GlobalTheory.NLink.rowsAD_in_setting <;> assumption)
end

