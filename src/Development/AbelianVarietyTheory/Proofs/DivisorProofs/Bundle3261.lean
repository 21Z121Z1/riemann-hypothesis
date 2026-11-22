import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystem
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_evA_eq_of_presents (k : Type) [CommRing k] (σ : Type) [Finite σ]
    (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n)
    (hy : ∀ n i, IsNilpotent (y n i)) (r : ∀ n, B (n + 1) →ₐ[k] B n)
    (hr : ∀ n i, r n (y (n + 1) i) = y n i) (hP : Presents k y hy) (b : ∀ n, B n)
    (hb : ∀ n, r n (b (n + 1)) = b n) :
    ∃! f : MvPowerSeries σ k, ∀ n, evA k (y n) (hy n) f = b n := by
  classical
  have hX : ∀ n i, evA k (y n) (hy n) (X i) = y n i := by
    intro n i
    change constantCoeff (substAlgHom (R := k) (a := fun i => (C (y n i) : MvPowerSeries Empty (B n)))
      (hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hy n i) (X i)) = _
    rw [substAlgHom_X, constantCoeff_C]
  have hres : ∀ n f, r n (evA k (y (n + 1)) (hy (n + 1)) f) = evA k (y n) (hy n) f := fun n f =>
    (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (B (n + 1))).2 (B n) (r n) _ _ _ _ (hr n) f
  have hdown : ∀ n m, n ≤ m → ∀ f, evA k (y m) (hy m) f = b m → evA k (y n) (hy n) f = b n := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base => exact fun _ h => h
    | succ m _ ih =>
      intro f hf
      exact ih f (by rw [← hres, hf, hb])
  choose F hF using fun n => hP.1 n (b n)
  choose ν hν using hP.2
  have hcoef : ∀ (α : σ →₀ ℕ) (g g' : MvPowerSeries σ k),
      evA k (y _) (hy (ν (α.degree + 1))) g = b _ → evA k (y _) (hy (ν (α.degree + 1))) g' = b _ →
      coeff α g = coeff α g' := by
    intro α g g' h h'
    have := hν (α.degree + 1) (g - g') (by rw [map_sub, h, h', sub_self]) α (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  let f : MvPowerSeries σ k := fun α => coeff α (F (ν (α.degree + 1)))
  have hf : ∀ α, coeff α f = coeff α (F (ν (α.degree + 1))) := fun _ => rfl
  refine ⟨f, fun n => ?_, fun g hg => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ (B n) (evA k (y n) (hy n)) fun i => by
      rw [hX]; exact hy n i
    let m := max n ((Finset.range (N + 1)).sup ν)
    have h0 := hN (f - F m) fun α hα => by
      rw [map_sub, hf, sub_eq_zero]
      refine hcoef α _ _ (hF _) (hdown _ m ?_ _ (hF m))
      exact le_max_of_le_right (Finset.le_sup (f := ν) (Finset.mem_range.2 (by omega)))
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact hdown n m (le_max_left _ _) _ (hF m)
  · ext α
    rw [hf]
    exact hcoef α _ _ (hg _) (hF _)

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleCompatibleSectionsThickeningTowerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_compatible_sections_thickeningTower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → RelAmple (Y 0) (N 0) → ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ, c = a ∨ c = a + 1 → ∀ v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)), (∀ e, (v e).IsGen) → ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  first | exact @GlobalTheory.FormalAlg.TowerVA.exists_veryAmple_compatible | exact GlobalTheory.FormalAlg.TowerVA.exists_veryAmple_compatible | (intros; apply GlobalTheory.FormalAlg.TowerVA.exists_veryAmple_compatible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepDualPairCharactersBetaQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.WeilTripleW

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), pow_add, mul_assoc, hm, mul_one]

end GlobalTheory.WeilTripleW

theorem GlobalTheory.WeilTripleW.exists_isWeil : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (beta G i j) (beta G i j / alpha G t i j) om := by
  intro D T L sc G μ₀ hL t i j hS B hB X Y r s r' s' hX hY Mo hMo
  obtain ⟨hb, ha, rb, ra⟩ := GlobalTheory.SquareChars.square_chars hL t i j hS
  exact GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel D B hB _ _ X Y r s r' s' hX hY Mo hMo
    (beta G i j) (beta G i j / alpha G t i j) hb (GlobalTheory.WeilTripleW.isHecke_div hb ha) rb
    (GlobalTheory.WeilTripleW.resEtaPow_div rb ra)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepSquarePairCharactersAlphaQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} {n m : ℕ}
    (h : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (m + n) := by
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem squareWeil₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (alpha G t i j) (alpha G t i j / beta G i j) om := by
  intro D T L sc G μ₀ hL t i j _hst B hB X Y r s r' s' hX hY Mo hMo
  have hα : GlobalTheory.LFun.IsHecke D.host.F D.host.E (alpha G t i j) := by
    have hm := (hL.mu0 j).1
    have hx := (hL.xi t).1
    have he := hL.eta.1
    refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
    have e1 := hm.2 x
    have e2 := hx.2 x
    have e3 := he.2 x
    show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply]
    rw [e1, e2, e3]
    simp
  have hβ : GlobalTheory.LFun.IsHecke D.host.F D.host.E (beta G i j) := by
    have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
    have he := hL.eta.1
    refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
    have e1 := hc.2 x
    have e3 := he.2 x
    show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply, e1, e3]
    simp
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank hL t i j
  have pα := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rα
  have pβ := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rβ
  exact GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel D B hB _ _ X Y r s r' s' hX hY Mo hMo _ _ hα (isHecke_div hα hβ) pα (resEtaPow_div pα pβ)

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialAlgebraicityFromReciprocity
section
set_option autoImplicit false
noncomputable section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem expAlg : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ExpAlg := fun h1 h2 h3 h4 =>
  expAlg_of_serAlg (serAlg_of_ref (GlobalTheory.T.rational_series_of_reciprocity_hypotheses h1 h2 h3 h4) (GlobalTheory.T.scaleRoot_of_cuspRapidDecay_of_reciprocity_of_rayClassField h1 h2 h3 h4))

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendFiniteModif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extend_finiteModif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, TraitReg M G L (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb I _ k s hs
  exact GlobalTheory.T.locallyIntegralSections_extend_over_finiteModification R M G hsm hqc hgi L hL Y α t hpb I k s
    (fun i => GlobalTheory.T.locallyIntegral_of_regular_at_all_traits R M G hsm hqc hgi L hL Y α t hpb (k i) (s i) (hs i))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSectionExtendsNonzeroOfIntegralThetaConstan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmExt

theorem thList_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {x y : Sp K ⟶ S} (e : x = y) (θ : SecAt G L x) {N : ℕ} (pt : Fin N → (Over.mk x ⟶ G))
    (c : Fin N → K) (H : ThList G L ρ m x θ pt c) : ∃ pt' : Fin N → (Over.mk y ⟶ G), ThList G L ρ m y (e ▸ θ) pt' c := by
  subst e; exact ⟨pt, H⟩

theorem inj_comp {R V : Type} [CommRing R] [CommRing V] [IsDomain V] (φ : R →+* V) (hφ : Function.Injective φ) :
    Function.Injective ((algebraMap V (FractionRing V)).comp φ) := by
  rw [RingHom.coe_comp]; exact (IsFractionRing.injective V (FractionRing V)).comp hφ

theorem exists_fracMap {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsFractionRing.lift (inj_comp φ hφ), RingHom.ext fun r => by
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩

theorem secAt_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R : Type} [CommRing R] {x : Sp R ⟶ S}
    {τ₁ τ₂ : SecAt G L x} (h : SecM.ofSec G τ₁ = SecM.ofSec G τ₂) : τ₁ = τ₂ :=
  ThetaRuleCompare.sec_ext fun j => congrFun (congrArg Subtype.val h) j

theorem cast_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {Z : Scheme.{0}} {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {y₁ y₂ : Z ⟶ S} (e : y₁ = y₂) (u₁ : Over.mk y₁ ⟶ T) (u₂ : Over.mk y₂ ⟶ T)
    (hu : u₁.left = u₂.left) :
    SecM.ofSec G (VVRank.pullS G _ u₂ σ) = SecM.ofSec G (e ▸ VVRank.pullS G _ u₁ σ) := by
  subst e
  obtain rfl : u₁ = u₂ := Over.OverMorphism.ext hu
  rfl

theorem pull_pull_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R V K K' : Type} [CommRing R]
    [CommRing V] [CommRing K] [CommRing K'] (χ : Sp R ⟶ S) (σ : SecAt G L χ) (φ : R →+* V) (a : R →+* K)
    (b : V →+* K') (φK : K →+* K') (h : spMap φK ≫ spMap a ≫ χ = spMap b ≫ spMap φ ≫ χ)
    (hc : φK.comp a = b.comp φ) :
    SecM.ofSec G (SecAt.pull G L (SecAt.pull G L σ φ) b) = SecM.ofSec G (h ▸ SecAt.pull G L (SecAt.pull G L σ a) φK) := by
  simp only [SecAt.pull]
  rw [ThetaRuleCompare.pullS_comp, ThetaRuleCompare.pullS_comp]
  refine cast_pullS G L σ h _ _ ?_
  simp only [Over.comp_left, Over.homMk_left]
  rw [← spMap_comp, ← spMap_comp, hc]

theorem secAt_eq_of_generic {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) {V : Type}
    [CommRing V] [IsDomain V] (x : Sp V ⟶ S) (τ₁ τ₂ : SecAt G L x)
    (h : SecAt.pull G L τ₁ (algebraMap V (FractionRing V)) = SecAt.pull G L τ₂ (algebraMap V (FractionRing V))) :
    τ₁ = τ₂ := by
  have hDom : IsDominant (spMap (algebraMap V (FractionRing V))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).trans_le bot_le)⟩
  have hSD : IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    (isSchemeTheoreticallyDominant_iff_isDominant _).2 hDom
  have hFl : Flat (fst (Over.mk x) G).left := inferInstanceAs (Flat (pullback.fst x G.hom))
  let ιK : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ Over.mk x :=
    Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
  have hP := ThetaRuleCompare.isPullback_whisker (A := G) ιK
  refine ThetaRuleCompare.sec_ext fun j => BundleExt.fn_ext_dense (spMap (algebraMap V (FractionRing V)))
    (fst (Over.mk x) G).left fun Z ρ r z hrz hz => ?_
  let ρ' : Z ⟶ (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⊗ G).left := hP.lift ρ r hrz.symm
  have hfac : ρ' ≫ (ιK ▷ G).left = ρ := hP.lift_fst _ _ _
  have hz' : ρ' z ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x))).U j :=
    ThetaRuleCompare.chart_ge ιK j (show (ιK ▷ G).left (ρ' z) ∈ _ by rw [← Scheme.Hom.comp_apply, hfac]; exact hz)
  rw [← hfac, ← ThetaRuleCompare.gs_pullS ιK τ₁ ρ' z j hz', ← ThetaRuleCompare.gs_pullS ιK τ₂ ρ' z j hz']
  exact congrArg (fun u : SecAt G L (spMap (algebraMap V (FractionRing V)) ≫ x) => gs ρ' z _ (u.f j)) h

open GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace in
theorem mem_nonzeroLocus_of_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) (th : LB.Sec (LPow G L a T)) (z : (T' ⊗ G).left) (hz : z ∈ nonzeroLocus (VVRank.pullS G a h th)) :
    (h ▷ G).left z ∈ nonzeroLocus th := by
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ z).1 hz
  have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => a) th (h ▷ G).left
    (fun _ => whisker_snd_left G h) (𝟙 _) z j hj
  rw [Category.id_comp] at q
  have q' := q.trans (gs_stalkMap (h ▷ G).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left G h) j hj) _)
  refine (mem_nonzeroLocus _ _).2 ⟨j, wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T G).left) _
    (fun _ => whisker_snd_left G h) j hj, ?_⟩
  exact (isUnit_map_iff _ _).1 (q' ▸ u)

theorem spMap_closedPoint {R : Type} [CommRing R] (s : PrimeSpectrum R) {V : Type} [CommRing V] [IsLocalRing V]
    (φ₀ : Localization.AtPrime s.asIdeal →+* V) [IsLocalHom φ₀] :
    (spMap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal)))).base (IsLocalRing.closedPoint V) = s := by
  show PrimeSpectrum.comap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal))) (IsLocalRing.closedPoint V) = s
  rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint]
  ext1
  rw [PrimeSpectrum.comap_asIdeal]
  exact Localization.AtPrime.comap_maximalIdeal

theorem om_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R (FractionRing R)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R (FractionRing R) (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ χ θ pt c hodd h3 hm hPol hT hunit
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V)
      (φK : FractionRing R →+* FractionRing V)
      (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ),
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ →
      ∃ σ : SecAt t.G t.PP.L (spMap φ ≫ χ), SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) =
        SecM.ofSec t.G (h ▸ SecAt.pull t.G t.PP.L θ φK) ∧ NZ t.G t.PP.L (spMap φ ≫ χ) σ := by
    intro V _ _ _ hV φ φK h hc
    obtain ⟨pt₁, -, hT₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N _ _ φK _ θ pt _ hT
    obtain ⟨pt₂, hT₂⟩ := thList_cast t.G t.PP.L t.PP.rig m h _ pt₁ _ hT₁
    have hPF : PolFib t.G t.PP.L g (spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ) :=
      (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S t.G t.PP.L t.G t.PP.L (𝟙 S) (𝟙 _) t.PP.isLB t.PP.isLB (SiegLower.isGrpPullback_id _)
        (SiegLower.lbIso_pull_id t.PP.isLB) g (FractionRing R) _).2 _ φK hPol
    have hPF' : PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) := h ▸ hPF
    have hm' : IsUnit (m : V) := by simpa using hm.map φ
    have hcv : ∀ r, φK (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (φ r) :=
      fun r => congrArg (· r) hc
    have hPrim : Prim (algebraMap V (FractionRing V)) (fun a => φK (algebraMap R (FractionRing R) (c a))) := by
      obtain ⟨a, u, hu⟩ := hunit
      refine ⟨fun b => ?_, a, ?_, ?_⟩
      · dsimp only; rw [hcv]; exact RingHom.isIntegralElem_map _
      · dsimp only; rw [← hu]; exact ((u.isUnit.map (algebraMap R (FractionRing R))).map φK).ne_zero
      · dsimp only
        rw [← hu, hcv, show (algebraMap V (FractionRing V) (φ ↑u))⁻¹ = ((algebraMap V (FractionRing V)).comp φ) ↑u⁻¹ from
          (map_units_inv ((algebraMap V (FractionRing V)).comp φ) u).symm, RingHom.comp_apply]
        exact RingHom.isIntegralElem_map _
    exact GlobalTheory.T.exists_nonzero_section_closed_fibre_of_primitive_theta E H S t g m N V hV (spMap φ ≫ χ) (h ▸ SecAt.pull t.G t.PP.L θ φK) pt₂ _ hodd h3 hm' hPF' hT₂ hPrim
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_of_extends_over_complete_dvrs S t.G t.PP.L t.PP.isLB t.semi R χ θ
    (fun V _ _ _ hV φ φK h hc => (key V hV φ φK h hc).imp fun _ h' => h'.1)
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨p, hps⟩ : ∃ p : PrimeSpectrum R, (p : Sp R) = s := ⟨s, rfl⟩
  have hinjp : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : CharZero (Localization.AtPrime p.asIdeal) := charZero_of_injective_algebraMap hinjp
  obtain ⟨V, _, _, _, φ₀, hV, hinj, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (Localization.AtPrime p.asIdeal)
  obtain ⟨φ, hφdef⟩ : ∃ φ : R →+* V, φ = φ₀.comp (algebraMap R (Localization.AtPrime p.asIdeal)) := ⟨_, rfl⟩
  have hφ : Function.Injective φ := by
    rw [hφdef, RingHom.coe_comp]; exact hinj.comp hinjp
  obtain ⟨φK, hc⟩ := exists_fracMap φ hφ
  have h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hc]
  obtain ⟨σV, hσV, z, hz₁, hz₂⟩ := key V hV φ φK h hc
  have hθ : SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R)) = θ := secAt_ext t.G t.PP.L hσ
  have hFl : Flat t.G.hom := by haveI := t.semi.smooth; infer_instance
  have e₁ := pull_pull_cast t.G t.PP.L χ σ φ (algebraMap R (FractionRing R)) (algebraMap V (FractionRing V)) φK h hc
  rw [hθ] at e₁
  have heq : SecAt.pull t.G t.PP.L σ φ = σV :=
    secAt_eq_of_generic t.G t.PP.L _ _ _ (secAt_ext t.G t.PP.L (e₁.trans hσV.symm))
  subst heq
  refine ⟨((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ t.G).left z, ?_,
    mem_nonzeroLocus_of_pullS t.G _ _ σ z hz₂⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left, Scheme.Hom.comp_apply, hz₁]
  show (spMap φ) (IsLocalRing.closedPoint V) = s
  rw [← hps, hφdef]
  exact spMap_closedPoint p φ₀

end GlobalTheory.UMin.OmExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpenStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU E n)), IsOpen (L : Set (finU E n)) → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (L : Set (finU E n))) := by
  first | exact @GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | exact GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | (intros; apply GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_section_translates_cover_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.Mum.cover_by_translates | exact GlobalTheory.Mum.cover_by_translates | (intros; apply GlobalTheory.Mum.cover_by_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finite_omega_of_eq_zero {p : ℕ} {K : Type} [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) : Module.Finite K G.omega := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm

theorem finrank_rigExt_omega (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) :
    Module.Finite K G.omega ∧ Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
      Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  have h1 := finite_omega_of_eq_zero h G
  have h2 := finite_omega_of_eq_zero h G.dual
  have e1 : Module.finrank K G.omega = Module.finrank K (Cot K (G.A 1)) :=
    (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).finrank_eq
  have e2 : Module.finrank K G.dual.omega = Module.finrank K (Cot K (G.dual.A 1)) :=
    (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective h)).finrank_eq
  have hsum : Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
    rw [e1, e2]
    exact le_antisymm (GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height p K h G) (GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim p K h G)

  have hr := (G.rigToLie h).rank_range_add_rank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), rank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    (LinearEquiv.ofInjective _ (G.rigOfOmega_injective_of_eq_zero h)).rank_eq.symm] at hr
  have hfin : Module.Finite K G.RigExt := by
    haveI : Module.Free K G.RigExt := Module.Free.of_divisionRing K _
    rw [← Module.rank_lt_aleph0_iff, ← hr]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 K _) (Module.rank_lt_aleph0 K _)
  refine ⟨h1, hfin, ?_, hsum⟩
  have e := (G.rigToLie h).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), finrank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    LinearMap.finrank_range_of_inj (G.rigOfOmega_injective_of_eq_zero h)] at e
  rw [← e, ← hsum, add_comm, Subspace.dual_finrank_eq]

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProdStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_coords_bijective_onto_chart_prod : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  first | exact @GlobalTheory.FlagCell2.cellMap_image_eq | exact GlobalTheory.FlagCell2.cellMap_image_eq | (intros; apply GlobalTheory.FlagCell2.cellMap_image_eq <;> assumption)
end

