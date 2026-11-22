import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerTopStepChartConditionsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberFormsLayer_topStep_chart_conditions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 = (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top | exact GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ConjMet

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.ShFam.FlagCpt
open scoped ComplexOrder

theorem map_conj_eq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : M.map (starRingEnd ℂ) = Mᴴᵀ := by
  ext a b; simp

theorem mix_map_conj {m : ℕ} (s : ℝ) (M₀ M : Matrix (Fin m) (Fin m) ℂ) :
    mix s (M₀.map (starRingEnd ℂ)) (M.map (starRingEnd ℂ)) = (mix s M₀ M).map (starRingEnd ℂ) := by
  ext a b; simp [mix]

theorem dualGram_map_conj {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    dualGram (M.map (starRingEnd ℂ)) = (dualGram M).map (starRingEnd ℂ) := by
  rw [dualGram, dualGram, map_conj_eq, map_conj_eq, ← transpose_nonsing_inv (Mᴴ), ← conjTranspose_nonsing_inv]
  ext a b; simp

theorem mixDual_map_conj {m : ℕ} (s : ℝ) (M₀ M : Matrix (Fin m) (Fin m) ℂ) :
    mixDual s (M₀.map (starRingEnd ℂ)) (M.map (starRingEnd ℂ)) = (mixDual s M₀ M).map (starRingEnd ℂ) := by
  rw [mixDual, mixDual, dualGram_map_conj, dualGram_map_conj, mix_map_conj, dualGram_map_conj]

theorem smul_gram_map_conj {m : ℕ} (b : ℝ) (T : Matrix (Fin m) (Fin m) ℂ) :
    (b : ℂ) • ((T.map (starRingEnd ℂ))ᴴ * T.map (starRingEnd ℂ)) = ((b : ℂ) • (Tᴴ * T)).map (starRingEnd ℂ) := by
  ext a c; simp [Matrix.mul_apply, map_sum]

theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext Complex.conj_conj))

theorem conj_comp_conj {A : Type} [CommRing A] (σ : A →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ :=
  RingHom.ext fun a => Complex.conj_conj (σ a)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_conj_symm {σ σ' : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} {f : EigFrame Z σ x} {f' : EigFrame Z σ' x'}
    (h : f.IsMap (starRingEnd ℂ) f') : f'.IsMap (starRingEnd ℂ) f := fun τ i => by
  rw [h, GlobalTheory.GradedPieces.dual_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
    RingHom.ext Complex.conj_conj, spMap_dualMap_id, Category.id_comp]

variable {σ σ' : c.F →+* ℂ} {y : CxPts (genStr Z) σ} {y' : CxPts (genStr Z) σ'}

theorem gen_eq (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    y'.1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι Z := by
  rw [e, Category.assoc]

theorem gen_eq' (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    y.1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ y'.1 ≫ genι Z := by
  rw [e, ← Category.assoc, ← Category.assoc, spMap_conj_conj, Category.id_comp]

theorem r_conj [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (hσ : σ' = (starRingEnd ℂ).comp σ)
    (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : x.r σ' y' = x.r σ y := by
  subst hσ
  let j : CxPts (genStr Z) σ → CxPts (genStr Z) ((starRingEnd ℂ).comp σ) :=
    fun z => ⟨spMap (starRingEnd ℂ) ≫ z.1, by rw [Category.assoc, z.2, ← Spec.map_comp]; rfl⟩
  have hj : IsConjMap j := fun _ => rfl
  have hy : j y = y' := Subtype.ext e.symm
  simp only [OddPrimesWithRootsOfUnity.r, fun i => x.nrm_conj _ _ j hj i y, hy]

end Free

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_conj {R : Type} [CommRing R] {φ : c.F →+* R} {x0 : Sp R ⟶ Z.X} {f : EigFrame Z φ x0} {ψ : R →+* ℂ}
    {σ₁ σ₂ : c.F →+* ℂ} {x1 x2 : Sp ℂ ⟶ Z.X} {g : EigFrame Z σ₁ x1} {g' : EigFrame Z σ₂ x2}
    (h : f.Tri ψ g 1) (hg : g.IsMap (starRingEnd ℂ) g') (hσ : σ₂ = (starRingEnd ℂ).comp σ₁)
    (hx : x2 = spMap (starRingEnd ℂ) ≫ x1) : f.Tri ((starRingEnd ℂ).comp ψ) g' 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hx, h1, ← Category.assoc, spMap_comp_spMap], by rw [hσ, h2]; rfl, fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
  refine ⟨fun k => starRingEnd ℂ (cf k), by simp [c1], fun k hk => by simp [c2 k hk], ?_⟩
  have := GlobalTheory.GradedPieces.comb_map (starRingEnd ℂ) hx.symm c3
  simpa only [GlobalTheory.GradedPieces.dual_comp, ← hg τ i] using this

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : FlagCpt Z e} {σ σ' : F →+* ℂ} {p : Y.Y.pts σ} {p' : Y.Y.pts σ'}

theorem emb_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) : σ' = (starRingEnd ℂ).comp σ := by
  have h : spMap ((starRingEnd ℂ).comp σ) = spMap σ' := by
    rw [← p'.2, e', Category.assoc, p.2, ← Spec.map_comp]; rfl
  exact (EigLoc.spMap_inj h).symm

theorem embOf_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    embOf e σ' = (starRingEnd ℂ).comp (embOf e σ) := by
  rw [emb_conj e']; rfl

theorem base_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) : Var.base p' = Var.base p := by
  show p'.1 _ = p.1 _
  rw [e']
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))

theorem down_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    (Y.down p').1 = spMap (starRingEnd ℂ) ≫ (Y.down p).1 := by
  show p'.1 ≫ Y.π = _
  rw [e', Category.assoc]; rfl

theorem met_h_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) {G : EigMet Z (embOf e σ)} {G' : EigMet Z (embOf e σ')}
    (hG : ∀ (g : Y.FrameAt p) (g' : Y.FrameAt p') τ, g.IsMap (starRingEnd ℂ) g' →
      G'.gram (Y.down p') g' τ = (G.gram (Y.down p) g τ).map (starRingEnd ℂ))
    (n : Letter Dw → ℤ) {a : Y.Y.Fnˣ} (ha : p ∈ Var.eqnSet σ (divOf Y n) a) :
    (Y.met G' n).h a p' = (Y.met G n).h a p := by
  have hb : Var.base p' = Var.base p := base_conj e'
  obtain ⟨q, h1, h2⟩ := Y.exists_adapted p
  obtain ⟨φ, f, ta, tb⟩ := h2
  obtain ⟨g', hg'⟩ := q.2.exists_isMap (starRingEnd ℂ) (embOf_conj e') (gen_eq (down_conj e'))
  have hp : p'.1 = spMap ((starRingEnd ℂ).comp (Var.evStalk p)) ≫ stalkPt Y.Y (Var.base p) := by
    rw [e', ← Y.spMap_evStalk p, ← Category.assoc, spMap_comp_spMap]
  obtain ⟨ad', hv⟩ := adapted_of_tri hp ta (tri_conj tb hg' (embOf_conj e') (gen_eq (down_conj e')))
  have ha' : p' ∈ Var.eqnSet σ' (divOf Y n) a := by
    show (divOf Y n).IsEqn (Var.base p') a
    rw [hb]; exact ha
  have hP := prodPow_mem n h1
  have hP' := prodPow_mem n ad'.mem_eqnSet
  rw [(Y.met G' n).trans a _ p' ha' hP', (Y.met G n).trans a _ p ha hP, met_h G' n ad', met_h G n ⟨φ, f, ta, tb⟩]
  have hgen : Y.genSq G' n g' = Y.genSq G n q.2 := by
    unfold FlagCpt.genSq
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [hG q.2 g' z.1 hg', grSq_map_conj]
  have h0 := Var.tv_ne_zero ha hP
  rw [Var.tv] at h0
  obtain ⟨r, -, hr⟩ := Var.val_cx_ne_zero_iff.1 h0
  have htv : ‖Var.tv a (prodPow q.1 n) p'‖ = ‖Var.tv a (prodPow q.1 n) p‖ := by
    rw [Var.tv, Var.tv, ← hr, hv, (Var.hasVal_cx_stalk (y := p) r).val_eq, RingHom.comp_apply, Complex.norm_conj]
  rw [htv, hgen]

end Flag

section Tor

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
  {σ σ' : κ.c.F →+* ℂ} {y : CxPts (genStr s.T.Z) σ} {y' : CxPts (genStr s.T.Z) σ'}
  {g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)} {g' : EigFrame s.T.Z σ' (y'.1 ≫ genι s.T.Z)}

theorem eigMet_conj (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hg : g.IsMap (starRingEnd ℂ) g')
    (τ : D.host.E →+* ℂ) : (x.eigMet σ').gram y' g' τ = ((x.eigMet σ).gram y g τ).map (starRingEnd ℂ) :=
  OddPrimesWithRootsOfUnity.gram_conj x e g g' τ (hg τ)

theorem hodge_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (hg : g.IsMap (starRingEnd ℂ) g') (τ : D.host.E →+* ℂ) :
    (x.hodge σ').gram y' g' τ = ((x.hodge σ).gram y g τ).map (starRingEnd ℂ) := by
  by_cases hb : LiesIn y (genBd s.T.Z)
  · rw [x.hodge_gram_of_liesIn ((liesIn_iff_of_comp e _).2 hb), x.hodge_gram_of_liesIn hb]
    exact OddPrimesWithRootsOfUnity.gram_conj x e g g' τ (hg τ)
  · obtain ⟨f', hf'⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 (fun h => hb ((liesIn_iff_of_comp e _).1 h))
    obtain ⟨f, hfm⟩ := f'.exists_isMap (starRingEnd ℂ) (φ' := σ) (x' := y.1 ≫ genι s.T.Z)
      (by rw [hσ, conj_comp_conj]) (gen_eq' e)
    have hf : IsHodgeFrame s.U y f := hf'.conj hσ e (isMap_conj_symm hfm)
    rw [x.hodge_gram hf' g' τ, x.hodge_gram hf g τ, (isMap_conj_symm hfm).co τ hg (gen_eq e)]
    exact smul_gram_map_conj _ _

theorem wt_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (R : ℝ) :
    x.wt σ' R y' = x.wt σ R y := by
  rw [ToroidalCompactificationData.wt, ToroidalCompactificationData.wt, liesIn_iff_of_comp e, r_conj x hσ e]

theorem eigMetAt_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (hg : g.IsMap (starRingEnd ℂ) g') (τ : D.host.E →+* ℂ) (R : Option ℝ) :
    (x.eigMetAt σ' R).gram y' g' τ = ((x.eigMetAt σ R).gram y g τ).map (starRingEnd ℂ) := by
  cases R with
  | none => exact hodge_conj x hσ e hg τ
  | some R =>
    simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
    rw [wt_conj x hσ e R, hodge_conj x hσ e hg τ, eigMet_conj x e hg τ]
    split_ifs
    exacts [mix_map_conj _ _ _, mixDual_map_conj _ _ _]

end Tor

end GlobalTheory.ShFam.ConjMet

open GlobalTheory.ShFam.ConjMet in

theorem GlobalTheory.ShFam.mets_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ σ' : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ) (p : Pts (Φ.C k).Y σ) (p' : Pts (Φ.C k).Y σ') (a : (Φ.C k).Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ (divOf (Φ.C k) n) a → (∀ R, Var.Met.h (metsOf x Φ k R σ' n) a p' = Var.Met.h (metsOf x Φ k R σ n) a p) ∧ Var.Met.h (refMet x Φ k σ' n) a p' = Var.Met.h (refMet x Φ k σ n) a p ∧ rFlag x Φ k σ' p' = rFlag x Φ k σ p := by
  intro D A N j S κ s x Φ k σ σ' n p p' a e' ha
  have hσ := embOf_conj (Y := Φ.C k) e'
  have hd := down_conj (Y := Φ.C k) e'
  exact ⟨fun R => met_h_conj e' (fun g g' τ hg => eigMetAt_conj x hσ hd hg τ R) n ha,
    met_h_conj e' (fun g g' τ hg => eigMet_conj x hd hg τ) n ha, r_conj x hσ hd⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulEqOneOfSubst
section
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.GradedPieces GlobalTheory.LieMet
open GlobalTheory.ArcQ (Wit LieImg ArcBasis)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints (EpsPt IsLetters IsCombGt)

namespace GlobalTheory.LocM.FJ.FlagIndep

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X}
  {k : Type} [Field k] {y : Sp k ⟶ X} {m : ℕ}

theorem eig_of_comb {v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t y (v i)) {lam : 𝓞 E → k}
    (he : ∀ i a, v i ≫ (t.act.act a).left = spMap (epsMul (lam a)) ≫ v i) {cf : Fin m → k}
    {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsTanAtG t y w) (hc : IsCombAtG t y v cf w) (a : 𝓞 E) :
    w ≫ (t.act.act a).left = spMap (epsMul (lam a)) ≫ w := by
  have key : ∀ i, actR t.act a (tanOf (hv i)) = lam a • tanOf (hv i) := fun i => tan_ext (he i a)
  have e := (comb_iff hv cf hw).1 hc
  have : actR t.act a (tanOf hw) = lam a • tanOf hw := by
    rw [e, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, key, smul_comm]
  exact congrArg (fun z => (tv z).left) this

end Tangent

section Arcs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p}

def cst (F : DVF p) : F.O →+* LaurentSeries ↥F.K := F.toLaurent.comp PowerSeries.C

variable {b : Z.i.c.V W →+* F.O} {a : ArcIn Dw Z.i.l (Z.i.c.V W).subtype F.O b} {χ : Sp (PowerSeries F.O) ⟶ (Y Z.i).X}

def arcVec (Wt : Wit (Y Z.i) a χ) (w : epsR (PowerSeries F.O) ⟶ Wt.t.G) :
    Sp (DualNumber (LaurentSeries ↥F.K)) ⟶ (Y Z.i).t.G.left :=
  spMap (dualMap F.toLaurent) ≫ w.left ≫ Wt.m.φ

end Arcs

section Series

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p}

theorem linInd_of_frame {X : Scheme.{0}} {t : SAB H X} {k : Type} [Field k] {y : Sp k ⟶ X} {l : Level H} {c : Coeff l}
    {f : c.F →+* k} {v : Vecs Dw t k} (h : IsFrame t f y v) (τ : E →+* ℂ) :
    LinearIndependent k fun i => tanOf (h.1 τ i).1 := by
  refine Fintype.linearIndependent_iffₛ.2 fun c c' e => ?_
  have hw := isTan_tv (∑ i, c i • tanOf (h.1 τ i).1)
  have hc : IsCombAtG t y (v τ) c (tv (∑ i, c i • tanOf (h.1 τ i).1)).left :=
    (comb_iff (fun i => (h.1 τ i).1) c hw).2 rfl
  have hc' : IsCombAtG t y (v τ) c' (tv (∑ i, c i • tanOf (h.1 τ i).1)).left :=
    (comb_iff (fun i => (h.1 τ i).1) c' hw).2 e
  exact fun i => congrFun ((h.2 τ _ hw (eig_of_comb (fun i => (h.1 τ i).1) (fun j a => (h.1 τ j).2 a) hw hc)).unique hc hc') i

variable (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ} {Mo : Z.X.Modules}
  (T : GrTriv Z e Mo) (f : Γ(Mo, Z.genO))

end Series

end GlobalTheory.LocM.FJ.FlagIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closure_of_embedding : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (C : Coc Z) (N : ℕ), Nonempty (C.Emb N) → ∀ (ch : Charts Z) (r : ℕ) (D : C.Sub ch r), Nonempty (D.Closure s) := by
  first | exact @GlobalTheory.nonempty_subClosure | exact GlobalTheory.nonempty_subClosure | (intros; apply GlobalTheory.nonempty_subClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, 0 ≤ c i) → ∑ i, c i • toReal (γ i) ∈ psdCone bar X := by
  first | exact @GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | exact GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | (intros; apply GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDense
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

theorem mem_of_ι {X : Scheme.{0}} (U : X.Opens) (t : U.toScheme) : U.ι t ∈ U := by
  have := Set.mem_range_self (f := U.ι) t
  rwa [Scheme.Opens.range_ι] at this

theorem lift_of_isIso_over {S T Z N V : Scheme.{0}} (s : Z ⟶ S) (P : T ⟶ S) [Flat P] (f : N ⟶ Z) (g : N ⟶ S)
    (hg : f ≫ s = g) (U : Z.Opens) [IsIso (f ∣_ U)] [IsLocallyNoetherian N]
    (hW : Dense ((f ⁻¹ᵁ U : N.Opens) : Set N))
    (jV : V ⟶ pullback s P) [IsOpenImmersion jV] (hd : Dense (Set.range jV))
    (hU : ∀ v, pullback.fst s P (jV v) ∈ U)
    (r : pullback g P ⟶ pullback s P) (hr1 : r ≫ pullback.fst s P = pullback.fst g P ≫ f)
    (hr2 : r ≫ pullback.snd s P = pullback.snd g P) :
    ∃ jN : V ⟶ pullback g P, IsOpenImmersion jN ∧ Dense (Set.range jN) ∧ jN ≫ r = jV ∧
      r ⁻¹' Set.range jV = Set.range jN := by
  let UK : (pullback s P).Opens := pullback.fst s P ⁻¹ᵁ U
  let φ : U.toScheme ⟶ N := inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hφ : φ ≫ f = U.ι := by
    simp only [φ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hret : ∀ {T' : Scheme.{0}} (x : T' ⟶ N) (y : T' ⟶ U.toScheme), y ≫ U.ι = x ≫ f → y ≫ φ = x := by
    intro T' x y hxy
    have hrange : Set.range x ⊆ Set.range (f ⁻¹ᵁ U).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← hxy, Scheme.Hom.comp_apply]
      exact mem_of_ι U _
    have hh : IsOpenImmersion.lift (f ⁻¹ᵁ U).ι x hrange ≫ (f ⁻¹ᵁ U).ι = x := IsOpenImmersion.lift_fac _ _ _
    have hh2 : IsOpenImmersion.lift (f ⁻¹ᵁ U).ι x hrange ≫ f ∣_ U = y := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hh, hxy]
    rw [← hh, ← hh2]
    simp only [φ, Category.assoc, IsIso.hom_inv_id_assoc]
  have hyK : (pullback.fst s P ∣_ U) ≫ U.ι = UK.ι ≫ pullback.fst s P := morphismRestrict_ι _ _
  let g' : UK.toScheme ⟶ pullback g P := pullback.lift ((pullback.fst s P ∣_ U) ≫ φ) (UK.ι ≫ pullback.snd s P)
    (by rw [← hg]; simp only [Category.assoc]; rw [reassoc_of% hφ, reassoc_of% hyK, pullback.condition])
  have hg'r : g' ≫ r = UK.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr1, pullback.lift_fst_assoc, Category.assoc, hφ, hyK]
    · rw [Category.assoc, hr2, pullback.lift_snd]
  have he : (r ∣_ UK) ≫ UK.ι = (r ⁻¹ᵁ UK).ι ≫ r := morphismRestrict_ι _ _
  have hg'range : Set.range g' ⊆ Set.range (r ⁻¹ᵁ UK).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hg'r]
    exact mem_of_ι UK t
  have hk : IsOpenImmersion.lift (r ⁻¹ᵁ UK).ι g' hg'range ≫ (r ⁻¹ᵁ UK).ι = g' := IsOpenImmersion.lift_fac _ _ _
  haveI : IsIso (r ∣_ UK) := by
    refine ⟨⟨IsOpenImmersion.lift (r ⁻¹ᵁ UK).ι g' hg'range, ?_, ?_⟩⟩
    · rw [← cancel_mono (r ⁻¹ᵁ UK).ι, Category.assoc, hk, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc]
        apply hret
        rw [Category.assoc, hyK, ← Category.assoc, he, Category.assoc, hr1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, he, Category.assoc, hr2]
    · rw [← cancel_mono UK.ι, Category.assoc, he, ← Category.assoc, hk, hg'r, Category.id_comp]
  have hjVrange : Set.range jV ⊆ Set.range UK.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    exact hU v
  have hjV' : IsOpenImmersion.lift UK.ι jV hjVrange ≫ UK.ι = jV := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (IsOpenImmersion.lift UK.ι jV hjVrange) := by
    haveI : IsOpenImmersion (IsOpenImmersion.lift UK.ι jV hjVrange ≫ UK.ι) := by rw [hjV']; infer_instance
    exact IsOpenImmersion.of_comp _ UK.ι
  let jN : V ⟶ pullback g P := IsOpenImmersion.lift UK.ι jV hjVrange ≫ inv (r ∣_ UK) ≫ (r ⁻¹ᵁ UK).ι
  have hjNr : jN ≫ r = jV := by
    simp only [jN, Category.assoc, ← he, IsIso.inv_hom_id_assoc, hjV']
  have hrange : r ⁻¹' Set.range jV = Set.range jN := by
    ext p
    constructor
    · rintro ⟨v, hv⟩
      have hpU : p ∈ r ⁻¹ᵁ UK := by
        rw [Scheme.Hom.mem_preimage, ← hv]
        exact hU v
      obtain ⟨q, rfl⟩ : p ∈ Set.range (r ⁻¹ᵁ UK).ι := by rw [Scheme.Opens.range_ι]; exact hpU
      have hq : (r ∣_ UK) q = IsOpenImmersion.lift UK.ι jV hjVrange v := by
        apply UK.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply, ← hv, ← Scheme.Hom.comp_apply, hjV']
      refine ⟨v, ?_⟩
      simp only [jN, Scheme.Hom.comp_apply, ← hq]
      rw [show (inv (r ∣_ UK)) ((r ∣_ UK) q) = q from Scheme.hom_inv_apply (asIso (r ∣_ UK)) q]
    · rintro ⟨v, rfl⟩
      exact ⟨v, by rw [← Scheme.Hom.comp_apply, hjNr]⟩
  have hsub : ∀ p ∈ r ⁻¹ᵁ UK, p ∈ closure (Set.range jN) := by
    intro p hp
    obtain ⟨q, rfl⟩ : p ∈ Set.range (r ⁻¹ᵁ UK).ι := by rw [Scheme.Opens.range_ι]; exact hp
    rw [mem_closure_iff]
    intro O hO hqO
    have hS : IsOpen ((r ⁻¹ᵁ UK).ι ⁻¹' O) := hO.preimage (r ⁻¹ᵁ UK).ι.continuous
    have hT : IsOpen (UK.ι '' ((r ∣_ UK) '' ((r ⁻¹ᵁ UK).ι ⁻¹' O))) :=
      UK.ι.isOpenEmbedding.isOpenMap _ ((r ∣_ UK).isOpenEmbedding.isOpenMap _ hS)
    obtain ⟨_, ⟨_, ⟨s0, hs0, rfl⟩, rfl⟩, v, hv⟩ := hd.inter_open_nonempty _ hT ⟨_, ⟨_, ⟨q, hqO, rfl⟩, rfl⟩⟩
    refine ⟨(r ⁻¹ᵁ UK).ι s0, hs0, ?_⟩
    rw [← hrange]
    exact ⟨v, by rw [hv, ← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]⟩
  have hdense : Dense (Set.range jN) := by
    intro p
    obtain ⟨w, hwW, hwn⟩ := exists_specializes_of_dense_scheme N _ (f ⁻¹ᵁ U).isOpen hW (pullback.fst g P p)
    obtain ⟨p', hp'p, hp'w⟩ := Flat.generalizingMap (pullback.fst g P) hwn
    apply hp'p.mem_closed isClosed_closure
    apply hsub
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hr1, Scheme.Hom.comp_apply, hp'w]
    exact hwW
  exact ⟨jN, inferInstance, hdense, hjNr, hrange⟩

theorem lifts_to_normalisation : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (Z X' N V : Scheme.{0})
    (s : Z ⟶ Sp R) (b : X' ⟶ Z) (ν : N ⟶ X') (U : Z.Opens) (jV : V ⟶ pullback s (spMap (algebraMap R K))),
    IsLocallyNoetherian N → IsOpenImmersion jV → Dense (Set.range jV) →
    (∀ v, pullback.fst s (spMap (algebraMap R K)) (jV v) ∈ U) → IsIso (b ∣_ U) → IsIso (ν ∣_ (b ⁻¹ᵁ U)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ U) : N.Opens) : Set N) →
    ∃ jN : V ⟶ pullback (ν ≫ b ≫ s) (spMap (algebraMap R K)), IsOpenImmersion jN ∧ Dense (Set.range jN) ∧
      jN ≫ pullback.map (ν ≫ b ≫ s) (spMap (algebraMap R K)) s (spMap (algebraMap R K)) (ν ≫ b) (𝟙 _) (𝟙 _)
        (by simp) (by simp) = jV ∧
      pullback.map (ν ≫ b ≫ s) (spMap (algebraMap R K)) s (spMap (algebraMap R K)) (ν ≫ b) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ⁻¹' Set.range jV = Set.range jN := by
  intro R K _ _ _ _ _ Z X' N V s b ν U jV hN hjV hjVd hjVU hb hν hWd
  haveI := hN; haveI := hjV; haveI := hb; haveI := hν
  haveI : IsIso ((ν ≫ b) ∣_ U) := by rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hb
  haveI : Flat (spMap (algebraMap R K)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  exact lift_of_isIso_over s (spMap (algebraMap R K)) (ν ≫ b) (ν ≫ b ≫ s) (Category.assoc _ _ _) U hWd jV hjVd hjVU _
    (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans (Category.comp_id _))

end GlobalTheory.BlowOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydiscStatement
section
open GlobalTheory.ShFam.Hor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  first | exact @GlobalTheory.periodVec_extends | exact GlobalTheory.periodVec_extends | (intros; apply GlobalTheory.periodVec_extends <;> assumption)
end

