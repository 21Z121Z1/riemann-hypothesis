import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0071
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0703
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TwistUnr

theorem nat_not_mem_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (Q : HeightOneSpectrum (𝓞 E)) (hq' : ((q : ℕ) : 𝓞 E) ∈ Q.asIdeal) : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal := by
  intro hp'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply Q.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left a hp') (Q.asIdeal.mul_mem_left b hq')

theorem unrAt_xiTw : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  intro B f T v Q k hg hQ
  have hp : B.host.pde.Prime := B.toPre.level_prime _ B.host.pde_level.1
  have hp' : B.host.pde'.Prime := B.toPre.level_prime _ B.host.pde_level.2
  have h1 := nat_not_mem_of_ne hp (B.host.g_prime k) (B.host.pde_ne_g k).1 Q hg
  have h2 := nat_not_mem_of_ne hp' (B.host.g_prime k) (B.host.pde_ne_g k).2 Q hg
  have hψ : (T.psi v).UnrAt Q := ((T.psi_is v).ram Q).2 hQ
  unfold TwDat.xiTw
  split_ifs
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel.unr Q h1) hψ

end GlobalTheory.TwistUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlacesUnionRamifiedPlacesFinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem overPl_subsingleton {L : Type} [Field L] (w : HeightOneSpectrum (𝓞 L)) :
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) | NG.OverPl w v}.Subsingleton := by
  intro v hv v' hv'
  exact HeightOneSpectrum.ext (hv.symm.trans hv')

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem gPl_union_qPl_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  intro D η
  have hS : (⋃ k : Fin 2, placesOver D.host.E (D.host.g k)).Finite :=
    Set.finite_iUnion fun k => placesOver_finite_of_ne_zero _ _ (D.host.g_prime k).ne_zero
  have hR : {w | ¬ η.UnrAt w}.Finite := GlobalTheory.Mem.UnrAe.finite_ramified η
  refine Set.Finite.union ?_ ?_
  · refine (hS.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨w, hw, k, hk⟩
    exact Set.mem_biUnion (Set.mem_iUnion.2 ⟨k, hk⟩) hw
  · refine (hR.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨_, w, hw, hu⟩
    exact Set.mem_biUnion (x := w) hu hw

end GlobalTheory.LevCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up.TypesAt

theorem typesTrue_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) : TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  have h1 := t.r.z.lev.C
  have hg := t.grp
  rw [h1]
  have h2 := w.C_eq
  rw [h2]
  exact hg

theorem types_atMem : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ _ => TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  intro _ hL
  refine EvG.imp evG_good fun K _ _ _ _ _ => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T _ _ _ _ _ w Z Wt p0 t nch n xd c _ _ _
  exact typesTrue_rows t

end GlobalTheory.HeightCounting.Up.TypesAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesWithLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Fin

theorem types_withLoc : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ {o : P.q.Over} (m : Moved o), m.Copy → m.Coh → ∀ (s : Side0 o) (r : ReadPk m s), r.Pin → TypesTrue (withLoc L).ntypes m.z.R.C.P m.z.R.C.W := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ o m _ _ s r _
  rw [m.z.lev.C, w.C_eq]
  have hg : TypesTrue x.o.N.ntypes f.P f.W := x.fits.grp
  exact ⟨fun k v => hg.pl k v, fun k => hg.teich k, fun k v j => hg.chi k v j, fun k p => hg.ser k p⟩

end GlobalTheory.HeightCounting.Fin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentHolomorphicBoundedDomain
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

namespace GlobalTheory.UnifHolo

theorem holo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (W : X.X.Opens) (g : Γ(X.X, W)), DifferentiableOn ℂ (ev X.str (σ.comp e.toRingHom) W g ∘ ψ) (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ W g
  classical
  haveI : IsOpenImmersion j := hL.1
  have hjr : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by
    have := (hU.2.1 k).1
    omega
  let L : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) ≃L[ℂ]
      (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set B := L.symm ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) hjr (Equiv.refl _) hp (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a c) B := fun τ a c =>
    ((TorHolo.differentiable_stdMat (U.X k) hjr (Equiv.refl _) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show ReciprocityTheory.ChartRestriction.G.FD.mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  have hY : IsHolTo B fun b => (cxPt T.Z (U.un k (x b))).1 := GlobalTheory.GramFamily.isHolTo_cxPt T.Z hU k hB x hd
  have hflat : ∀ u : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat u) = u := by
    intro u; funext ⟨i, a, b⟩; rfl
  have hrel : ∀ b ∈ B, cxOf e σ hj (ψ (L.symm b)) = cxPt T.Z (U.un k (x b)) := by
    intro b hb
    have h1 := hψ (x b)
    rwa [domPt_stdFrame (U.X k) hjr (Equiv.refl _) hp hb, hflat] at h1
  set g' := (j.appIso W).inv.hom g with hg'
  intro v hv
  have hb : L v ∈ B := by
    refine Set.mem_preimage.2 ?_
    rw [L.symm_apply_apply]
    exact hv.1
  have hS : L v ∈ {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ W)} := by
    refine ⟨hb, ?_⟩
    rw [← hrel _ hb, L.symm_apply_apply]
    exact le_preimage_cxOf e σ hj W hv.2
  have hdA : DifferentiableAt ℂ (fun b => valAt' (cxPt T.Z (U.un k (x b))).1 (j ''ᵁ W) g') (L v) :=
    ((hY (j ''ᵁ W) g').2 (L v) hS).differentiableAt (((hY (j ''ᵁ W) g').1).mem_nhds hS)
  have hc := (hdA.comp v L.differentiableAt).differentiableWithinAt
    (s := DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W)
  have heq : ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W,
      (ev X.str (σ.comp e.toRingHom) W g ∘ ψ) w =
        ((fun b => valAt' (cxPt T.Z (U.un k (x b))).1 (j ''ᵁ W) g') ∘ L) w := by
    intro w hw
    have hwB : L w ∈ B := by
      refine Set.mem_preimage.2 ?_
      rw [L.symm_apply_apply]
      exact hw.1
    rw [Function.comp_apply, Function.comp_apply, ev_eq_valAt'_cxOf e σ hj W g hw.2, ← hrel _ hwB,
      L.symm_apply_apply]
  exact hc.congr heq (heq v hv)

end GlobalTheory.UnifHolo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Ring

variable {O : Type} [CommRing O] {x : Sp O ⟶ X}

theorem base_eq (x : Sp O ⟶ X) (I : Ideal O) : spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x =
    spMap (algebraMap (O ⧸ I) (DualNumber (O ⧸ I))) ≫ spMap (Ideal.Quotient.mk I) ≫ x := by
  rw [← Category.assoc, Guard.sp_comp]

theorem red_ex (I : Ideal O) {v : Sp (DualNumber O) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk I)) ≫ v :=
  ⟨Over.homMk (spMap (dualMap (Ideal.Quotient.mk I)) ≫ v)
    ((GlobalTheory.FactorDepth.isTanAtG_map t (Ideal.Quotient.mk I) hv).1.trans (base_eq x I).symm), rfl⟩

theorem red_tors (I : Ideal O) {q : ℕ} (hq : (q : O) ∈ I) {v : Sp (DualNumber O) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ t.G)
    (hw : w.left = spMap (dualMap (Ideal.Quotient.mk I)) ≫ v) : w ^ q = 1 := by
  have hv' := GlobalTheory.FactorDepth.isTanAtG_map t (Ideal.Quotient.mk I) hv
  have h0 := smT_zero_ovT hv'
  have key : ∀ n : ℕ, smT _ (n : O ⧸ I) (ovT hv') = ovT hv' ^ n := fun n => by
    induction n with
    | zero => rw [Nat.cast_zero, pow_zero]; exact h0
    | succ n ih => rw [Nat.cast_succ, smT_add _ _ h0, ih, smT_unit, pow_succ]
  have hq0 : (q : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hq
  have h1 : ovT hv' ^ q = 1 := by rw [← key, hq0, h0]
  let δ : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ x) ⟶ tEpsG (spMap (Ideal.Quotient.mk I) ≫ x) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (base_eq x I).symm)
  have h2 : w = Formalism.L2.Pj.preHom δ (ovT hv') := Over.OverMorphism.ext (hw.trans (Category.id_comp _).symm)
  rw [h2, ← map_pow, h1, map_one]

def res {q q' : ℕ} (h : q ∣ q') (c : TorsChar t x q') : TorsChar t x q where
  χ := c.χ
  mul B _ _ _ g g' hg hg' := by
    obtain ⟨k, rfl⟩ := h
    exact c.mul B g g' (by rw [pow_mul, hg, one_pow]) (by rw [pow_mul, hg', one_pow])
  nat B B' _ _ _ _ _ _ φ g g' hg hg' := by
    obtain ⟨k, rfl⟩ := h
    exact c.nat B B' φ g g' (by rw [pow_mul, hg, one_pow]) hg'

theorem dlog_down {p k n : ℕ} (hk : k ≤ n) (c : TorsChar t x (p ^ n)) (c₁ : TorsChar t x (p ^ k))
    (hc : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
      (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G), w ^ (p ^ k) = 1 → c.χ B w = c₁.χ B w)
    {g : ℕ} {e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) {D : Fin g → O}
    (hD : DlogIs t p n c e D) : DlogIs t p k c₁ e D := by
  intro a v hav w hw
  have hv := Guard.comb_tan he hav
  obtain ⟨w', hw'⟩ := red_ex (Ideal.span {(p : O) ^ n}) hv
  have hle : Ideal.span {(p : O) ^ n} ≤ Ideal.span {(p : O) ^ k} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hk)
  let φ : DualNumber (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] DualNumber (O ⧸ Ideal.span {(p : O) ^ k}) :=
    { dualMap (Ideal.Quotient.factor hle) with
      commutes' := fun r => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'] }
  have h1 := c.nat _ _ φ w' w (red_tors _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w' hw') (by
    rw [hw, hw', ← Category.assoc, Guard.sp_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, φ])
  rw [← hc _ w (red_tors _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w hw), h1]
  have h2 := hD a v hav w' hw'
  have h3 : ∀ z, (φ z).snd = Ideal.Quotient.factor hle z.snd := fun z => by simp [φ, dualMap]
  rw [h3, h2, Ideal.Quotient.factor_mk]

end Ring

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp ↥(intO C) ⟶ X}

theorem coords {g : ℕ} {e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)} (he : IsTanBasis t x e) {a : Fin g → C}
    {w : Sp (DualNumber C) ⟶ t.G.left}
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w) (s : C)
    {vO : Sp (DualNumber ↥(intO C)) ⟶ t.G.left} (hv : IsTanAtG t x vO)
    (hs : spMap (dualMap (intO C).subtype) ≫ vO = spMap (epsMul s) ≫ w) :
    ∃ b : Fin g → ↥(intO C), IsCombAtG t x e b vO ∧ ∀ i, (b i : C) = s * a i := by
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have h := he.2 _ (RingHom.id ↥(intO C)) vO
  simp only [h1, h3, Category.id_comp] at h
  obtain ⟨b, hb, -⟩ := h hv
  have heC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (he.1 j)
  have h4 := Guard.comb_smul heC hw s
  rw [← hs] at h4
  exact ⟨b, hb, congrFun ((he.2 C _ _ (GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hv)).unique
    (GlobalTheory.LatDRFree.comb_map t (intO C).subtype hb) h4)⟩

theorem mem_latHT_iff : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [CompleteSpace C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (x : Sp ↥(intO C) ⟶ X), (∀ x' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x → x' = x) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)), IsTanBasis t x e → ∀ (n : ℕ) (h : Fin n → Fin g → ↥(intO C)), (∀ c : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c e (h j)) → (∀ j, ∃ c : TorsChar t x (p ^ 1), DlogIs t p 1 c e (h j)) → ∀ (a : Fin g → C) (w : Sp (DualNumber C) ⟶ t.G.left), IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO C).subtype ≫ x) ↔ (∀ j, ‖∑ i, (h j i : C) * a i‖ ≤ 1) ∧ ∀ i, ‖(p : C) * a i‖ ≤ 1) := by
  intro hB E _ _ _ H X _ t p hp C _ _ _ _ _ hn x hx g e he n h hc hj a w hw
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  constructor
  · intro hL
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    have hpa : ∀ i, ‖(p : C) * a i‖ ≤ 1 := by
      obtain ⟨x', hx', vO, hv, hs⟩ := hB E H X t p C hn x hx w hL p (by
        rw [hn, ← Real.rpow_neg_one]
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
        rw [div_le_one (by linarith)]
        linarith)
      obtain rfl := hx x' hx'
      obtain ⟨b, -, hb⟩ := coords he hw _ hv hs
      exact fun i => hb i ▸ (b i).2
    refine ⟨fun j => ?_, hpa⟩
    obtain ⟨x', hx', m, vO, hv, hs, hd⟩ := hL
    obtain rfl := hx x' hx'
    obtain ⟨b, hbv, hb⟩ := coords he hw _ hv hs
    show _ ∈ intO C
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h j i).2 ?_
      have := (b i).2
      rwa [hb, pow_zero, _root_.one_mul] at this
    obtain ⟨c, hcj⟩ := hj j
    obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t C x' (p ^ 1) (p ^ m) (pow_ne_zero _ hp.out.ne_zero) (pow_dvd_pow _ hm) c
    obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x' p m c' g e he.1
    have hδ := (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x' p 1 c g e he.1).2 D (h j) (dlog_down hm c' c hc' he.1 hD) hcj
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    obtain ⟨w', hw'⟩ := red_ex (Ideal.span {(p : ↥(intO C)) ^ m}) hv
    have h1 := hd m c' w' hw'
    have h2 : (p : ↥(intO C) ⧸ Ideal.span {(p : ↥(intO C)) ^ m}) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [hD b vO hbv w' hw', h2, Ideal.span_singleton_zero, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
    have h3 : ∑ i, (D i : C) * a i = r := by
      apply mul_right_cancel₀ (pow_ne_zero m hp0)
      have := congrArg (intO C).subtype hr
      simp only [map_mul, map_pow, map_natCast, map_sum, Subring.subtype_apply, hb] at this
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h4 : ∑ i, (h j i : C) * a i = r - ∑ i, (δ i : C) * ((p : C) * a i) := by
      rw [← h3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO C).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (a i) * this
    rw [h4]
    exact Subring.sub_mem _ r.2 (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (δ i).2 (hpa i))
  · rintro ⟨h1, h2⟩
    let b : Fin g → ↥(intO C) := fun i => ⟨(p : C) * a i, h2 i⟩
    obtain ⟨vO, hv, hbv⟩ := Guard.exists_comb he.1 b
    have heC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (he.1 j)
    refine ⟨x, rfl, 1, vO, hv, ?_, fun k c w' hw' => ?_⟩
    · rw [pow_one]
      exact Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO C).subtype hbv) (Guard.comb_smul heC hw p)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (↥(intO C) ⧸ Ideal.span {(p : ↥(intO C)) ^ 0}) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
      rw [Subsingleton.elim (TrivSqZeroExt.snd _) 0]
      exact Ideal.zero_mem _
    obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p k c g e he.1
    obtain ⟨j, hcj⟩ := hc (res (pow_dvd_pow p hk) c)
    have hδ := (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p 1 _ g e he.1).2 D (h j)
      (dlog_down hk c _ (fun _ _ _ _ _ _ => rfl) he.1 hD) hcj
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    let s : ↥(intO C) := ⟨∑ i, (h j i : C) * a i, h1 j⟩
    have h3 : ∑ i, D i * b i = (s + ∑ i, δ i * b i) * (p : ↥(intO C)) ^ 1 := by
      apply (intO C).subtype_injective
      simp only [map_mul, map_pow, map_natCast, map_sum, map_add, Subring.subtype_apply, s, b]
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO C).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (-(p : C) * a i) * this
    rw [hD b vO hbv w' hw', h3, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.HTLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricLowerDetUnitAndSuperdiagIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaUnit

theorem val_det_block {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Fintype ι] [DecidableEq ι]
    (v : Valuation K Γ) (p : ι → Prop) [DecidablePred p] (A B : Matrix ι ι K)
    (hA : ∀ a b, v (A a b) ≤ 1) (hB : ∀ a b, v (B a b) ≤ 1) (hAB : A * B = 1)
    (hlow : ∀ a b, p a → ¬ p b → v (A a b) < 1) :
    v (Matrix.of fun a b : {x // p x} => A a.1 b.1).det = 1 := by
  let O := v.valuationSubring
  let A' : Matrix ι ι O := Matrix.of fun a b => ⟨A a b, hA a b⟩
  let B' : Matrix ι ι O := Matrix.of fun a b => ⟨B a b, hB a b⟩
  have hAB' : A' * B' = 1 := by
    ext a b
    have := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.one_apply] at this ⊢
    rw [AddSubmonoidClass.coe_finsetSum, apply_ite (fun x : O => (x : K))]
    simpa [A', B'] using this
  let f := IsLocalRing.residue O
  have hf : ∀ a b, p a → ¬ p b → f (A' a b) = 0 := by
    intro a b ha hb
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact hlow a b ha hb
  let A₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => A' a.1 b.1
  let B₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => B' a.1 b.1
  have h1 : f.mapMatrix A₁ * f.mapMatrix B₁ = 1 := by
    ext a b
    have h := congrArg f (congrFun (congrFun hAB' a.1) b.1)
    rw [Matrix.mul_apply, map_sum, ← Fintype.sum_subtype_add_sum_subtype p] at h
    rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ p x}))
      (fun c _ => by rw [map_mul, hf a.1 c.1 a.2 c.2, zero_mul]), add_zero] at h
    rw [Matrix.mul_apply]
    simp only [map_mul] at h
    refine Eq.trans h ?_
    simp only [Matrix.one_apply, Subtype.ext_iff]
    split_ifs <;> simp
  have h2 : f A₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, ← RingHom.map_det, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h3 : ((A₁.det : O) : K) = (Matrix.of fun a b : {x // p x} => A a.1 b.1).det := by
    have := RingHom.map_det O.subtype A₁
    exact this
  rw [← h3]
  refine le_antisymm A₁.det.2 (not_lt.1 fun hlt => h2 ?_)
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact hlt

theorem detDD_unit_supDiag_int : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  intro L _ _ _ n r s h hp
  have key : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring →
      ∀ a b, Valued.v (g.val a b) ≤ 1 := by
    rintro g ⟨x, rfl⟩ a b
    exact (x.val a b).2
  have hA := key h hp.1
  have hB := key h⁻¹ (inv_mem hp.1)
  refine ⟨?_, ?_⟩
  · exact val_det_block Valued.v (fun x : Fin n => r ≤ x.val) h.val (h⁻¹).val hA hB (by simp)
      (fun a b ha hb => hp.2 a b ha (not_le.1 hb))
  · unfold NG.supDiag
    refine Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun b _ => ?_
    split_ifs
    · exact hA a b
    · simp

end GlobalTheory.ParaUnit
end

