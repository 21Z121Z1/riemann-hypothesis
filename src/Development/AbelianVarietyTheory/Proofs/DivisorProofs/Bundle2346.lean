import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinFSndFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SquareComm

noncomputable section
namespace GlobalTheory.StageDict

theorem isFinF_snd_frames : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn false FA').cart τ = X.rA'.s τ) →
    (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t) := by
  intro D T A A' WW X ψ θ α β νH S FA' FW hA' hW hI t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [hA' τ, hW τ]
  exact hF
end GlobalTheory.StageDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteTwistedKernelCubeLambda
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerFinite

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    (x y : Y ⟶ A) : evc hP x y = lam (cls L hL) x y := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem add_inv_eq_of_same {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a a' : Y ⟶ A) (t : Y ⟶ T)
    (h₁ : Same A (abelian₂ A L) N a t) (h₂ : Same A (abelian₂ A L) N a' t) :
    CechPic.pull a.left (cls L hL) + CechPic.pull (a⁻¹).left (cls L hL) =
      CechPic.pull a'.left (cls L hL) + CechPic.pull (a'⁻¹).left (cls L hL) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e := ((same_iff hP hN a t).1 h₁).trans ((same_iff hP hN a' t).1 h₂).symm
  rw [evc_lam hL hP, evc_lam hL hP] at e
  have e' := congrArg (CechPic.pull (lift (a⁻¹ * a'⁻¹) (𝟙 Y)).left) e
  simp only [pull_lam, lift_fst, lift_snd_assoc, Category.id_comp] at e'
  simp only [lam] at e'
  rw [show a⁻¹ * a'⁻¹ * a = a'⁻¹ by rw [mul_right_comm, inv_mul_cancel, _root_.one_mul],
    show a⁻¹ * a'⁻¹ * a' = a⁻¹ from inv_mul_cancel_right _ _] at e'
  linear_combination (norm := abel) e'.symm

theorem isFinite_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  intro R _ _ A _ hB L hL hA T _ _ N hN H h hh hH
  haveI := hB.comm
  have := hB.proper
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A L hL).1 hA
  have hAT : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback A.hom T.hom
  have : IsProper (snd A T).left := MorphismProperty.of_isPullback hAT inferInstance
  have : IsAffineHom (fst A T).left := MorphismProperty.of_isPullback hAT.flip inferInstance
  let f : H.left ⟶ T.left := (h ≫ snd A T).left
  have hf : f ≫ T.hom = H.hom := Over.w (h ≫ snd A T)
  have : IsProper f := inferInstanceAs (IsProper (h.left ≫ (snd A T).left))
  change IsFinite f
  suffices LocallyQuasiFinite f from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (f ⁻¹' {z}) with h0 | ⟨x₀, hx₀⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField x₀
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField x₀
  let g : Spec (CommRingCat.of K) ⟶ T.left := y₀ ≫ f
  let π : pullback f g ⟶ H.left := pullback.fst f g
  let q : pullback f g ⟶ Spec (CommRingCat.of K) := pullback.snd f g
  let Z : Scheme.{0} := pullback f g
  have hpb : IsPullback π q f g := IsPullback.of_hasPullback f g
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  let P : Over (Sp R) := Over.mk (y₀ ≫ H.hom)
  let Q : Over (Sp R) := Over.mk (π ≫ H.hom)
  let yo : P ⟶ H := Over.homMk y₀ rfl
  let qo : Q ⟶ P := Over.homMk q (by
    show q ≫ y₀ ≫ H.hom = π ≫ H.hom
    rw [← hf, ← Category.assoc π, hpb.w]
    simp only [g, Category.assoc])
  let p₁ : Q ⟶ H := Over.homMk π rfl
  have hpt : p₁ ≫ h ≫ snd A T = qo ≫ yo ≫ h ≫ snd A T := by
    ext
    exact hpb.w
  let w : H ⟶ A := h ≫ fst A T
  have hs₁ : Same A (abelian₂ A L) N (p₁ ≫ w) (p₁ ≫ h ≫ snd A T) :=
    (hH _ _ _).2 ⟨p₁, by ext <;> simp [w]⟩
  have hs₂ : Same A (abelian₂ A L) N (qo ≫ yo ≫ w) (p₁ ≫ h ≫ snd A T) := by
    rw [hpt]
    exact (hH _ _ _).2 ⟨qo ≫ yo, by ext <;> simp [w]⟩
  have key := add_inv_eq_of_same hL hN.isLB _ _ _ hs₁ hs₂
  rw [← GrpObj.comp_inv qo, Over.comp_left _ _ _ qo, Over.comp_left _ _ _ qo, pull_comp qo.left,
    pull_comp qo.left, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w).left,
    GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w)⁻¹.left, map_zero, add_zero] at key
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (p₁ ≫ w).left := inferInstanceAs (IsAffineHom (π ≫ h.left ≫ (fst A T).left))
  have : Z.IsQuasiAffine := GlobalTheory.AmpleStabFinite.quasiAffine_of_pull_add (p₁ ≫ w).left ((p₁ ≫ w)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [GlobalTheory.AmpleStabFinite.cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add]
      exact (congrArg _ key).trans (zsmul_zero _))
  have : IsAffine Z := GlobalTheory.AmpleStabFinite.isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set Z).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun v hv => ?_
  have e : f v = g (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = x₀ := Scheme.fromSpecResidueField_apply x₀ _
    exact (show f v = z from hv).trans ((show f x₀ = z from hx₀).symm.trans (congrArg f e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) v _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.TwistKerFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsClosedImmersion
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem fibre_isIso {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
    [IsClosedImmersion f] [GeometricallyConnected s] [Surjective (f ≫ s)] {g g' : ℕ}
    (hg' : SmoothOfRelativeDimension g' s) (hg : SmoothOfRelativeDimension g (f ≫ s))
    (hle : g' ≤ g) (K : Type) [Field K] [Algebra R K] :
    IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))) := by
  have H₁ := IsPullback.of_hasPullback f (pullback.fst s (spMap (algebraMap R K)))
  have H₂ := IsPullback.of_hasPullback s (spMap (algebraMap R K))
  have H := H₁.paste_vert H₂
  have h₁ : SmoothOfRelativeDimension g' (pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H₂ hg'
  have h₂ : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback H hg
  have : Surjective (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := MorphismProperty.of_isPullback H ‹_›
  have : Smooth s := hg'.smooth
  have : AlgebraicGeometry.IsIntegral (Limits.pullback s (spMap (algebraMap R K))) := GlobalTheory.isIntegral_of_isPullback_of_smooth H₂
  have : Smooth (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := h₂.smooth
  have : AlgebraicGeometry.IsReduced (Limits.pullback f (pullback.fst s (spMap (algebraMap R K)))) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K)))
  have : Nonempty ↥(Limits.pullback (C := Scheme.{0}) f (pullback.fst s (spMap (algebraMap R K)))) := by
    obtain ⟨z, -⟩ := (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))).surjective (default : PrimeSpectrum K)
    exact ⟨z⟩
  exact GlobalTheory.DivisiblePart.isIso_of_dim_le _ _ h₁ h₂ hle

end GlobalTheory.AbMonoIso

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} [IsLocallyNoetherian S] (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    [Flat (f ≫ p)] {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have : Smooth p := hg'.smooth
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : IsLocallyNoetherian (Limits.pullback p j) := isLocallyNoetherian_of_isOpenImmersion gX
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_isProper s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g g' : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g' B'.hom → g' ≤ g → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S _ B B' _ _ hB hB' g g' hg hg' hle x _ _
  have := hB.proper
  have := hB.smooth
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : Flat (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) hle
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem IsDual.eq_of_evc {S : Scheme.{0}} {A B' T : Over S} [GrpObj A] [GrpObj B'] {P' : LB (A ⊗ B').left}
    (h : IsDual A B' P') {y₁ y₂ : T ⟶ B'}
    (e : evc h.isLB (fst A T) (snd A T ≫ y₁) = evc h.isLB (fst A T) (snd A T ≫ y₂)) : y₁ = y₂ := by
  have hM : (ev P' (fst A T) (snd A T ≫ y₁)).IsLB := pull_isLB h.isLB _
  have ha : IsAdditive (ev P' (fst A T) (snd A T ≫ y₁)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
    rw [evc_ev h.isLB, evc_ev h.isLB, evc_ev h.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ y₁)
  exact (h.univ T _ hM ha).unique ((cls_eq_iff hM hM).1 rfl)
    ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)

theorem comp_mul_eq {S : Scheme.{0}} {G Y : Over S} [MonObj G] (f : Y ⟶ G ⊗ G) :
    f ≫ μ = (f ≫ fst G G) * (f ≫ snd G G) := by
  show _ = lift _ _ ≫ μ
  rw [lift_comp_fst_snd]

theorem isMonHom_of_classifying : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → IsAdditive (swap P') → P.IsLB →
    IsAdditive (swap P) → ∀ x : B ⟶ B', LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsMonHom x := by
  intro S A B B' _ _ _ P P' h' ha' hP ha x e
  have hP' := h'.isLB
  have hE : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB hP' _
  have c : cls P hP = cls _ hE := (cls_eq_iff hP hE).2 e
  have K : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B), evc hP a b = evc hP' a (b ≫ x) := by
    intro Y a b
    have k := evc_ev hP' (fst A B) (snd A B ≫ x) hE a b
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k, evc, evc, c]
  have hs : (swap P).IsLB := pull_isLB hP _
  have hs' : (swap P').IsLB := pull_isLB hP' _
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hP a (b * b') = evc hP a b + evc hP a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 ha Y b b' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at k
  have addR' : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B'),
      evc hP' a (b * b') = evc hP' a b + evc hP' a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs').1 ha' Y b b' a
    rwa [evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs'] at k
  have oneR : ∀ (Y : Over S) (a : Y ⟶ A), evc hP a (1 : Y ⟶ B) = 0 := fun Y a ↦ by
    rw [← evc_swap hP hs]; exact ha.evc_one hs a
  have oneR' : ∀ (Y : Over S) (a : Y ⟶ A), evc hP' a (1 : Y ⟶ B') = 0 := fun Y a ↦ by
    rw [← evc_swap hP' hs']; exact ha'.evc_one hs' a
  have u : ∀ (G : Over S) [MonObj G], snd A (𝟙_ (Over S)) ≫ (η : 𝟙_ (Over S) ⟶ G) = 1 := fun G _ ↦ by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over S))) (toUnit _)]
  refine ⟨?_, ?_⟩
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← K, u, u, oneR, oneR']
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← Category.assoc, comp_mul_eq, comp_mul_eq, ← K, addR, K, K, ← addR']
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjective
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
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefDescent

theorem exists_algebraic_point : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧ (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) :=
  GlobalTheory.T.exists_mem_fiber_isAlgebraic_residueField_of_lft

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) :=
  GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue

theorem exists_curve_over : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F),
    π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    topologicalKrullDim (Z : Set X) = 1 → ∃ C : Closeds Y, IsIrreducible (C : Set Y) ∧
      topologicalKrullDim (C : Set Y) = 1 ∧ π '' (C : Set Y) = (Z : Set X) := by
  intro F _ Y X π sX p hπ hX hY hs Z hZi hZd
  obtain ⟨hPX, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  subst hπ
  have : IsProper π := IsProper.of_comp π sX
  obtain ⟨η, hη⟩ := QuasiSober.sober hZi Z.isClosed
  obtain ⟨y₀, hy₀⟩ := π.surjective η
  obtain ⟨y, hy, halg⟩ := exists_algebraic_point Y X π y₀
  have hd := dim_closure_eq_of_isAlgebraic F Y X π sX y halg
  rw [hy, hy₀, hη.def] at hd
  refine ⟨Closeds.closure {y}, isIrreducible_singleton.closure, ?_, ?_⟩
  · exact hd.trans hZd
  · change π '' closure {y} = Z
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hy, hy₀, hη.def]

theorem isNef_of_pull : ∀ (F : Type) [Field F] [NumberField F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F) (L : LB X) (hL : L.IsLB) (L' : LB Y) (hL' : L'.IsLB), π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → CechPic.pull π (cls L hL) = cls L' hL' → (letI := algebraΓOfHom p; IsNef F L') → (letI := algebraΓOfHom sX; IsNef F L) := by
  intro F _ _ Y X π sX p L hL L' hL' hπ hX hY hs hcl hnef
  letI := algebraΓOfHom sX
  letI := algebraΓOfHom p
  have hnef' : IsNef F L' := hnef
  obtain ⟨hPX, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX
  obtain ⟨hPY, A', hA'⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hY
  have : IsProper (strHom F X) := by rwa [strHom_eq (f := sX) fun _ => rfl]
  have : IsProper (strHom F Y) := by rwa [strHom_eq (f := p) fun _ => rfl]
  refine ⟨hL, fun Z hZ => ?_⟩
  obtain ⟨C, hCi, hCd, hCZ⟩ := exists_curve_over F Y X π sX p hπ hX hY hs Z hZ.1 hZ.2
  have hC : IsCompleteCurve F C := (isCompleteCurve_iff (f := p) (fun _ => rfl)).2 ⟨hCi, hCd⟩
  by_contra hneg
  push_neg at hneg
  have hM := isLB_dual hL
  have hMpos : 0 < interNumRed F Z ![dual L] := by rw [hZ.interNumRed_dual hA hL]; linarith
  obtain ⟨r, hr, s, hs0⟩ := PosBaseChange.exists_hasNonzeroSec (k := F) hA hM hZ.1 hZ.2.le fun _ => hMpos
  have hr' := isLB_lbPow hM r
  have hZc : Closeds.closure (π '' (C : Set Y)) = Z := by
    ext1
    simp only [Closeds.coe_closure, hCZ, Z.isClosed.closure_eq]
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ π := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ π) (by
    rw [← hZc, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩
  have hsφ : Function.Surjective φ := fun z => by
    obtain ⟨y, hy, e⟩ := hCZ.ge ((range_redι Z).le ⟨z, rfl⟩)
    obtain ⟨y, rfl⟩ := (range_redι C).ge hy
    exact ⟨y, (redι Z).isClosedEmbedding.injective ((congrArg (fun q => q y) hφ).trans e)⟩
  have := isIntegral_red hC.1
  have := isIntegral_red hZ.1

  obtain ⟨z, hz⟩ : ∃ z, z ∉ nonzeroLocus s := by
    by_contra! h
    obtain ⟨t, ht⟩ := exists_isGen_of_nonzeroLocus_eq_top s (top_unique fun z _ => h z)
    have e0 := (cls_eq_zero_iff (LB.isLB_pull hr' (redι Z))).2 ⟨t, ht⟩
    have h1 : interNumRed F Z ![lbPow (dual L) r] = 0 := by
      letI := algebraΓAlong F (redι Z)
      rw [interNumRed_one_eq hr']
      exact interNum_eq_zero_of_cls_eq_zero F _ (isLB_vecOne (LB.isLB_pull hr' _)) 0 e0
    rw [hZ.interNumRed_lbPow hA hM] at h1
    have : (0 : ℤ) < r := by exact_mod_cast hr
    nlinarith
  letI := algebraΓAlong F (redι C)
  have := hC.isProper_strHom
  obtain ⟨x, hx⟩ := hsφ (genericPoint _)
  have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge (by
    change φ x ∈ nonzeroLocus s
    rw [hx]; exact (sec_ne_zero_iff s).1 hs0)
  obtain ⟨c, hc⟩ := hsφ z
  have h0 := (interNum_one_nonneg_of_sec (k := F) (hA'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hCd) (LB.isLB_pull (LB.isLB_pull hr' _) φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).2 (fun htop => hz (by
        have := (nonzeroLocus_secPull s φ).le (htop.ge (show c ∈ (⊤ : Opens _) from trivial))
        rw [← hc]; exact this))
  have hD' := isLB_dual hL'
  have hP' := isLB_lbPow hD' r
  have h1 : interNumRed F C ![lbPow (dual L') r] =
      interNum F (structureModule _) ![((lbPow (dual L) r).pull (redι Z)).pull φ] := by
    rw [interNumRed_one_eq hP']
    refine interNum_congr_cls F _ (isLB_vecOne (LB.isLB_pull hP' _))
      (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hr' _) φ)) fun i => ?_
    fin_cases i
    change pull (redι C) (cls _ hP') = pull φ (pull (redι Z) (cls _ hr'))
    rw [← pull_comp, hφ, pull_comp, cls_lbPow hD', cls_lbPow hM, cls_dual hL', cls_dual hL, ← hcl]
    simp only [map_nsmul, map_neg]
  rw [← h1, hC.interNumRed_lbPow hA' hD', hC.interNumRed_dual hA' hL'] at h0
  have h2 := hnef'.2 C hC
  have : (0 : ℤ) ≤ r := by positivity
  nlinarith

end GlobalTheory.NefDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoLiftSmallArtinExtensions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open IsLocalRing

namespace GlobalTheory.ArtinOpen

theorem stalk_hom_ext_of_mono {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) (R : CommRingCat.{0})
    [IsLocalRing R] (g₁ g₂ : X.presheaf.stalk x ⟶ R) [IsLocalHom g₁.hom] [IsLocalHom g₂.hom]
    (h : f.stalkMap x ≫ g₁ = f.stalkMap x ≫ g₂) : g₁ = g₂ := by
  have e : Spec.map g₁ ≫ X.fromSpecStalk x = Spec.map g₂ ≫ X.fromSpecStalk x := by
    rw [← cancel_mono f, Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, h]
  have e2 := (SpecToEquivOfLocalRing X R).symm.injective (a₁ := ⟨x, g₁, inferInstance⟩)
    (a₂ := ⟨x, g₂, inferInstance⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simpa using e3

theorem isOpenImmersion_of_lift : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f := by
  intro X Y f _ _ _ hlift
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Flat f := by
    refine (Flat.iff_flat_stalkMap f).2 fun x => ?_
    have hres := GlobalTheory.T.residueFieldMap_surjective_of_mono' f x
    refine GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow (f.stalkMap x).hom (fun n => GlobalTheory.T.exists_stalk_retraction_of_small_lifting f hlift x hres n) ?_
    intro n g₁ g₂ h₁ h₂ h
    have := stalk_hom_ext_of_mono f x
      (CommRingCat.of (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ (n + 1)))
      (CommRingCat.ofHom g₁) (CommRingCat.ofHom g₂) (by ext a; exact congr($h a))
    exact congrArg CommRingCat.Hom.hom this
  exact IsOpenImmersion.of_flat_of_mono f

end GlobalTheory.ArtinOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  first | exact @GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | exact GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | (intros; apply GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth <;> assumption)
end

