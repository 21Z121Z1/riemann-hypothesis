import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.Inputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.FourierJacobiDifferentiable
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmApproximationTransference
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
section
noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

open NumberField GlobalTheory.TorusExt

theorem genRel_target {F : Type} [Field F] {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type}
    [Fintype K] {ε : K → ℤ} {φ : B ⟶ B'} {Φ : B' ⟶ B₀} {wD : LB.Iso M' (M₀.pull Φ)} {w' : LB.Iso M (M'.pull φ)}
    {w : LB.Iso M (M₀.pull (φ ≫ Φ))} (T : Tri wD w' w) (hM₀ : M₀.IsLB) (hM' : M'.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hp : ∀ k, pt k ≫ φ = pt' k) (hc : ∀ k, pt' k ≫ Φ = 𝟙 _ ≫ pt₀ k)
    {t' : LB.Gen (LB.LinComb M' pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (H : PMaps wD pt' pt₀ ε t' t₀ (𝟙 _))
    (t : LB.Gen (LB.LinComb M pt ε)) (x : F) : GenRel w' t t' x ↔ GenRel w t t₀ x := by
  have z : Sp F := (default : PrimeSpectrum F)
  have pe : ∀ k, pt' k z = φ (pt k z) := fun k => congrArg (fun g => g z) (hp k).symm
  have key : ∀ (j₀ : K → M₀.ι) (i : K → M'.ι) (q : K → M.ι), (∀ k, Φ (φ (pt k z)) ∈ M₀.U (j₀ k)) →
      (∀ k, φ (pt k z) ∈ M'.U (i k)) → (∀ k, pt k z ∈ M.U (q k)) →
      (((∏ k, gw w' (pt k) z (i k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt q) (t.s q)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M' pt' i) (t'.s i)).val ↔
      ((∏ k, gw w (pt k) z (j₀ k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt q) (t.s q)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val) := by
    intro j₀ i q h₀ h₁ h₂
    have a := T.prod (ε := ε) (h' := 𝟙 _) (φ' := pt') (fun k => (hp k).trans (Category.id_comp _).symm) _ (𝟙 _) z j₀ i q
      h₀ h₁ h₂
    have b := H _ (𝟙 _) z j₀ i (fun k => by show Φ (pt' k z) ∈ _; rw [pe]; exact h₀ k)
      (fun k => by show pt' k z ∈ _; rw [pe]; exact h₁ k)
    simp only [Category.id_comp] at a b
    rw [a, b, _root_.mul_assoc, Units.val_mul (∏ k, gw wD (pt' k) z (j₀ k) (i k) ^ ε k),
      Units.val_mul (∏ k, gw wD (pt' k) z (j₀ k) (i k) ^ ε k), mul_left_comm, Units.mul_right_inj]
  rw [genRel_iff w' t t' x z, genRel_iff w t t₀ x z]
  refine ⟨fun h => ⟨fun k => by rw [← Category.assoc, hp, hc, Category.id_comp], fun q j₀ h₀ h₂ => ?_⟩,
    fun h => ⟨hp, fun q i h₁ h₂ => ?_⟩⟩
  · choose i hi using fun k => exists_chart hM' (φ (pt k z))
    exact (key j₀ i q h₀ hi h₂).1 (h.2 q i hi h₂)
  · choose j₀ hj using fun k => exists_chart hM₀ (Φ (φ (pt k z)))
    exact (key j₀ i q hj h₁ h₂).2 (h.2 q j₀ hj h₂)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {O' O'' : Type} [CommRing O'] [IsDomain O']
  [CommRing O''] [IsDomain O''] {b : O →+* O'} {f : O' →+* O''} {a : ArcIn D l β O' b} {a' : ArcIn D l β O'' (f.comp b)}
  {hD : IsPullDeg f a.D₀ a'.D₀}

section Witness

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {g : O'' →+* R} {f₀ : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}

set_option maxHeartbeats 1600000 in

theorem exists_witness (h : IsBC f a a' hD) (hf₀ : f₀ = g.comp f) (W : ArcWit Y a I f₀ u χ) :
    ∃ W' : ArcWit Y a' I g u χ, W'.t = W.t ∧ HEq W'.m W.m ∧ HEq W'.P W.P ∧ HEq (W'.φ ≫ proj hD) W.φ ∧
      (∀ y, HEq (W'.e y) (W.e (hD.xe y))) ∧
      ∃ w : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD)), HEq w W.w ∧ Tri hD.w W'.w w := by
  letI := H.starRing
  subst hf₀
  obtain ⟨t, m, P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩ := W
  have gpD := pull_grp hD
  have sq : φ ≫ a.D₀.P.A.hom = (P.D.toPre.P.A.hom ≫ spMap g) ≫ spMap f := by
    rw [s1.1.w, spMap_comp, Category.assoc]
  obtain ⟨φ', rfl, hb⟩ : ∃ φ' : P.D.toPre.P.A.left ⟶ a'.D₀.P.A.left, φ' ≫ proj hD = φ ∧
      φ' ≫ a'.D₀.P.A.hom = P.D.toPre.P.A.hom ≫ spMap g :=
    ⟨gpD.1.lift _ _ sq, gpD.1.lift_fst _ _ _, gpD.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback P.D.toPre.P.A a'.D₀.P.A (spMap g) φ' := gpD.cancel (s1.congr (spMap_comp f g) rfl) hb
  have he' : eSec P.D.toPre.P.A ≫ φ' = spMap g ≫ eSec a'.D₀.P.A := (cubeMapOf gp).e_comm
  have gD := (isGen_iff hD.w).1 hD.w_gen
  have g0 := (isGen_iff w).1 s2
  obtain ⟨w', T⟩ := exists_cancel a.D₀.P.isLB hD.w w gD g0 a'.D₀.P.isLB P.D.toPre.P.isLB
  have hc : ∀ y, (P.D.toPre.c (e (hD.xe y))).left ≫ φ' = spMap g ≫ (a'.D₀.c y).left := fun y => by
    refine gpD.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hD.c_pr, ← Category.assoc (spMap g), ← spMap_comp]
      exact s5 _
    · rw [Category.assoc, hb, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  refine ⟨⟨t, m, P, φ', he', w', h.xeL.trans e, gp, (isGen_iff w').2 (T.pgen_cancel a.D₀.P.isLB gD g0), ?_, fun x => ?_, hc,
    fun F _ _ _ _ uF ha hu => ?_⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl, w, HEq.rfl, T⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ proj hD) (spMap (g.comp f)) he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff hD.w _ (fun _ => eSec a.D₀.P.A) _ a'.D₀.rig a.D₀.rig (specOf f) _
      (rigPull_le (proj hD) (specOf f) hD.he a.D₀.P.L) (fun _ => rfl)).1 hD.w_rig
    rw [spMap_comp] at r₀
    exact (maps_iff w' _ (fun _ => eSec a'.D₀.P.A) _ P.D.toPre.rig a'.D₀.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' a'.D₀.P.L) (fun _ => rfl)).2 (T.pmaps_cancel a.D₀.P.isLB (fun _ => he') r₁ r₀)
  · refine gpD.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h.act x]
      exact (s4 x).trans (Category.assoc _ _ _)
    · rw [Category.assoc, Category.assoc, Over.w, hb, ← Category.assoc, Over.w]
  · obtain ⟨_, hK, -⟩ := h.etaA 0
    letI : Algebra (FractionRing O') F :=
      ((algebraMap (FractionRing O'') F).comp (algebraMap (FractionRing O') (FractionRing O''))).toAlgebra
    have hF : Compat f F := fun x => congrArg (algebraMap (FractionRing O'') F) (hK x)
    obtain ⟨k₁, k₂⟩ := s6 F uF (fun x => (hF x).trans (ha (f x))) hu
    have hj : jFK (R := R) F ≫ jK R ≫ spMap g = jFK (R := O'') F ≫ jK O'' := Compat.sq (φ := g) ha
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀' q x e1 e2 e3 e4 => ?_⟩
    · rw [h.be_eq]
      refine (genRel_target T a.D₀.P.isLB a'.D₀.P.isLB (fun _ => ?_) (fun _ => ?_) (pmaps_psi hD F hF.sq y) _ _).2
        (k₁ (hD.xe y))
      · show (jFK (R := R) F ≫ jK R ≫ (P.D.toPre.c (e (hD.xe y))).left) ≫ φ' = jFK (R := O'') F ≫ jK O'' ≫ (a'.D₀.c y).left
        rw [Category.assoc, Category.assoc, hc, ← Category.assoc (jK R), ← Category.assoc]
        exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
      · show (jFK (R := O'') F ≫ jK O'' ≫ (a'.D₀.c y).left) ≫ proj hD =
          𝟙 _ ≫ jFK (R := O') F ≫ jK O' ≫ (a.D₀.c (hD.xe y)).left
        rw [Category.id_comp, Category.assoc, Category.assoc, hD.c_pr, ← Category.assoc (jK O''), ← Category.assoc]
        exact (congrArg (· ≫ _) hF.sq).trans (Category.assoc _ _ _)
    · obtain ⟨p, hp, hσ'⟩ : ∃ p : QkPt a.D₀ (FractionRing O') k, IsPullQk hD p p₀ ∧
          ((k = l.A ∧ ∃ v, HEq p (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
            (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
              HEq p (a.eta v) ∧ σ = Y.oF.eta v)) := by
        rcases hσ with ⟨rfl, v, h₁, h₂⟩ | ⟨rfl, v, hv, h₁, h₂⟩
        · exact ⟨a.etaA v, eq_of_heq h₁ ▸ h.etaA v, Or.inl ⟨rfl, v, HEq.rfl, h₂⟩⟩
        · exact ⟨a.eta v, eq_of_heq h₁ ▸ h.eta v, Or.inr ⟨rfl, v, hv, HEq.rfl, h₂⟩⟩
      obtain ⟨q₀, hq₀, -⟩ := existsUnique_qkExt (F' := F) a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) p
      obtain ⟨hy, hg⟩ := hp.ext hF hq₀ e1
      have hy' : hD.xe q₀'.y = q₀.y := by rw [hy, AddEquiv.apply_symm_apply]
      refine k₂ yF hyF k p σ hσ' q₀ q x hq₀ (e2.trans (congrArg e hy')) (fun z => ?_) e4
      obtain ⟨z, rfl⟩ := hD.xe.surjective z
      obtain ⟨hψ, hm⟩ := hg.2 z
      have pm := (maps_iff hD.w _ _ _ (q₀'.g.s z) (q₀.g.s (hD.xe z)) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm
      have k' := e3 z
      rw [h.be_eq, hy'] at k'
      exact (genRel_target T a.D₀.P.isLB a'.D₀.P.isLB k'.1 hψ pm _ _).1 k'

end Witness

theorem exists_witness_baseChange (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    (h : IsBC f a a' hD) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') {i : O' →+* R} {i' : O'' →+* R'} {κ : R →+* R'}
    (hκ : Function.Injective κ) (hI : I.map κ ≤ I') (hi : κ.comp i = i'.comp f) {u : R} {u' : R'} (hu : κ u = u')
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I i u χ) :
    ∃ (W' : ArcWit Y a' I' i' u' (spMap κ ≫ χ)) (hD₁ : IsPullDeg κ W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (specOf κ)).obj W.t.G), IsMonHom bc.hom ∧ IsPullUnif κ hD₁ bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (specOf κ)) ≫ W.m.φ ∧
      (∀ y, hD₁.xe (W'.e y) = W.e (hD.xe y)) ∧ W'.φ ≫ proj hD = proj hD₁ ≫ W.φ ∧
      ∃ (w₁ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (proj hD₁ ≫ W.φ)))
        (w₂ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD))),
        HEq w₁ w₂ ∧ Tri W.w hD₁.w w₁ ∧ Tri hD.w W'.w w₂ := by
  subst hu
  obtain ⟨W₁, hD₁, bc, mb, pu, hm, he, w₁, hφ, hw, T₁⟩ :=
    W.baseChange CubePf.cubePull hP hU h5 (qkPullExists hG) polOActPull hR hR' κ hκ hI
  obtain ⟨W', ht, hm', hP', hφ', he', w₂, hw', T₂⟩ := exists_witness h hi W₁
  obtain ⟨t₁, m₁, P₁, φ₁, _, _, e₁, _⟩ := W₁
  obtain ⟨t', m', P', φ', he₀, w', e', sp⟩ := W'
  dsimp only at ht
  subst ht
  obtain rfl := eq_of_heq hm'
  obtain rfl := eq_of_heq hP'
  exact ⟨⟨_, _, _, φ', he₀, w', e', sp⟩, hD₁, bc, mb, pu, hm, fun y => (congrArg hD₁.xe (eq_of_heq (he' y))).trans (he _),
    (eq_of_heq hφ').trans hφ, w₁, w₂, (hw'.trans hw).symm, T₁, T₂⟩

theorem admissibleBase_powerSeries_span_X (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] :
    AdmBase (PowerSeries A) (Ideal.span {PowerSeries.X}) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

def IsArc (Y : Model Xo c β) {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} (a : ArcIn D l β A b) (ϖ : A)
    (χ : Sp (PowerSeries A) ⟶ Y.X) : Prop :=
  χ ≫ Y.s = spMap (PowerSeries.C (R := A)) ≫ spMap b ∧
  (∀ x : Sp (PowerSeries A), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧
  (∀ x : Sp (PowerSeries A), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) ∧
  Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := A)) PowerSeries.X χ

def IsArcBase (A : Type) [CommRing A] [IsDomain A] (ϖ : A) : Prop :=
  (IsField A ∧ ϖ = 1) ∨ (IsDiscreteValuationRing A ∧ Irreducible ϖ ∧ IsAdicComplete (Ideal.span {ϖ}) A)

theorem IsArcBase.isPrincipalIdealRing {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (h : IsArcBase A ϖ) :
    IsPrincipalIdealRing A := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    infer_instance
  · infer_instance

theorem IsArcBase.ne_zero {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (h : IsArcBase A ϖ) : ϖ ≠ 0 := by
  rcases h with ⟨-, rfl⟩ | ⟨-, h, -⟩
  exacts [one_ne_zero, h.ne_zero]

theorem IsArcBase.dvd_pow {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (h : IsArcBase A ϖ) {x : A} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∣ ϖ ^ n := by
  rcases h with ⟨h, rfl⟩ | ⟨_, h, -⟩
  · obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
    exact ⟨0, y, by rw [pow_zero, hy]⟩
  · obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx h
    exact ⟨n, hn.dvd⟩

section PowerSeries

theorem map_comp_C' (f : O' →+* O'') :
    (PowerSeries.map f).comp (PowerSeries.C (R := O')) = (PowerSeries.C (R := O'')).comp f :=
  RingHom.ext fun x => PowerSeries.map_C f x

theorem IsBC.injective (h : IsBC f a a' hD) : Function.Injective f := by
  obtain ⟨_, hK, -⟩ := h.etaA 0
  intro x y hxy
  apply IsFractionRing.injective O' (FractionRing O')
  apply (algebraMap (FractionRing O') (FractionRing O'')).injective
  rw [hK, hK, hxy]

theorem exists_witness_powerSeries (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    [IsPrincipalIdealRing O'] [IsPrincipalIdealRing O''] (h : IsBC f a a' hD) {χ : Sp (PowerSeries O') ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χ) :
    ∃ (W' : ArcWit Y a' (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O'')) PowerSeries.X
        (spMap (PowerSeries.map f) ≫ χ)) (hD₁ : IsPullDeg (PowerSeries.map f) W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (specOf (PowerSeries.map f))).obj W.t.G), IsMonHom bc.hom ∧
      IsPullUnif (PowerSeries.map f) hD₁ bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (specOf (PowerSeries.map f))) ≫ W.m.φ ∧
      (∀ y, hD₁.xe (W'.e y) = W.e (hD.xe y)) ∧ W'.φ ≫ proj hD = proj hD₁ ≫ W.φ ∧
      ∃ (w₁ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (proj hD₁ ≫ W.φ)))
        (w₂ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD))),
        HEq w₁ w₂ ∧ Tri W.w hD₁.w w₁ ∧ Tri hD.w W'.w w₂ :=
  exists_witness_baseChange hG hP hU h5 h (admissibleBase_powerSeries_span_X O') (admissibleBase_powerSeries_span_X O'')
    (PowerSeries.map_injective f h.injective)
    (by rw [Ideal.map_span, Set.image_singleton, PowerSeries.map_X]) (map_comp_C' f) (PowerSeries.map_X f) W

theorem IsArc.baseChange (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    (h : IsBC f a a' hD) {ϖ : O'} {ϖ' : O''} (hϖ : IsArcBase O' ϖ) (hϖ' : IsArcBase O'' ϖ')
    {χ : Sp (PowerSeries O') ⟶ Y.X} (hχ : IsArc Y a ϖ χ) : IsArc Y a' ϖ' (spMap (PowerSeries.map f) ≫ χ) := by
  have := hϖ.isPrincipalIdealRing
  have := hϖ'.isPrincipalIdealRing
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hχ
  have mem : ∀ (x : Sp (PowerSeries O'')) (s : PowerSeries O'),
      s ∈ (spMap (PowerSeries.map f) x).asIdeal ↔ PowerSeries.map f s ∈ x.asIdeal := fun _ _ => Iff.rfl
  refine ⟨?_, fun x => ?_, fun x hx => ?_, ?_⟩
  · rw [Category.assoc, h₁, ← Category.assoc, ← spMap_comp, map_comp_C', spMap_comp, spMap_comp, Category.assoc]
  · refine (h₂ (spMap (PowerSeries.map f) x)).trans ?_
    rw [mem, PowerSeries.map_X]
  · refine h₃ (spMap (PowerSeries.map f) x) fun hm => hx ?_
    rw [mem, map_mul, PowerSeries.map_X, PowerSeries.map_C] at hm
    rcases x.isPrime.mem_or_mem hm with hm | hm
    · obtain ⟨n, y, hy⟩ := hϖ'.dvd_pow ((map_ne_zero_iff f h.injective).2 hϖ.ne_zero)
      refine Ideal.mul_mem_right _ _ (x.isPrime.mem_of_pow_mem n ?_)
      rw [← map_pow, hy, map_mul]
      exact Ideal.mul_mem_right _ _ hm
    · exact Ideal.mul_mem_left _ _ hm
  · obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ _).1 h₄
    obtain ⟨W', -⟩ := exists_witness_powerSeries hG hP hU h5 h W
    exact (Y.hasArcData_iff _ _ _ _ _).2 ⟨W'⟩

end PowerSeries

end GlobalTheory.ArcPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFjNeZeroAtSplitPoint
section
namespace GlobalTheory.FJDetect

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma eq_at_imag_of_real_translation_invariant {ι : Type} [Fintype ι] (F : (ι → ℂ) → ℂ)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hreal : ∀ s ∈ U, ∀ t : ι → ℝ, F (s + fun i => (t i : ℂ)) = F s)
    (a : ι → ℝ) (hseg : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((u : ℂ) • fun i => I * (a i : ℂ)) ∈ U) :
    F (fun i => I * (a i : ℂ)) = F 0 := by
  set v : ι → ℂ := fun i => I * (a i : ℂ) with hv
  have hD : ∀ s ∈ U, ∀ t : ι → ℝ, fderiv ℂ F s (fun i => (t i : ℂ)) = 0 := by
    intro s hs t
    have hd : HasFDerivAt F (fderiv ℂ F s) s :=
      (hF.differentiableAt (hU.mem_nhds hs)).hasFDerivAt
    have hline : HasDerivAt (fun u : ℝ => s + (u : ℂ) • fun i => (t i : ℂ))
        (fun i => (t i : ℂ)) 0 := by
      have h0 : HasDerivAt (fun u : ℝ => (u : ℂ) • fun i => (t i : ℂ))
          ((1 : ℂ) • fun i => (t i : ℂ)) 0 := by
        have := (hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const (fun i => (t i : ℂ))
        simpa using this
      simpa using h0.const_add s
    have hd0 : HasFDerivAt F (fderiv ℂ F s) (s + ((0 : ℝ) : ℂ) • fun i => (t i : ℂ)) := by
      simpa using hd
    have h1 := (hd0.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hline
    have h2 : (fun u : ℝ => F (s + (u : ℂ) • fun i => (t i : ℂ))) = fun _ => F s := by
      funext u
      have := hreal s hs (fun i => u * t i)
      have he : (s + (u : ℂ) • fun i => (t i : ℂ)) = s + fun i => ((u * t i : ℝ) : ℂ) := by
        funext i; simp
      rw [he, this]
    have h3 : HasDerivAt (fun u : ℝ => F (s + (u : ℂ) • fun i => (t i : ℂ)))
        (fderiv ℂ F s (fun i => (t i : ℂ))) 0 := by
      simpa [Function.comp_def] using h1
    rw [h2] at h3
    exact h3.unique (hasDerivAt_const _ _)
  have hDv : ∀ s ∈ U, fderiv ℂ F s v = 0 := by
    intro s hs
    have : v = I • fun i => (a i : ℂ) := by funext i; simp [hv]
    rw [this, map_smul, hD s hs a, smul_zero]
  set g : ℝ → ℂ := fun u => F ((u : ℂ) • v) with hg
  have hderiv : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → HasDerivAt g 0 u := by
    intro u hu0 hu1
    have hs := hseg u hu0 hu1
    have hd : HasFDerivAt F (fderiv ℂ F ((u : ℂ) • v)) ((u : ℂ) • v) :=
      (hF.differentiableAt (hU.mem_nhds hs)).hasFDerivAt
    have hl : HasDerivAt (fun w : ℝ => (w : ℂ) • v) v u := by
      have := (hasDerivAt_id u).ofReal_comp.smul_const v
      simpa using this
    have h4 := (hd.restrictScalars ℝ).comp_hasDerivAt u hl
    have h5 : ((fderiv ℂ F ((u : ℂ) • v)).restrictScalars ℝ) v = 0 := hDv _ hs
    rw [h5] at h4
    exact h4
  have hconst := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := 1)
    (fun u hu => (hderiv u hu.1 hu.2).continuousAt.continuousWithinAt)
    (fun u hu => (hderiv u hu.1 hu.2.le).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [hg] using hconst

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_mem_D1set_fj_ne_zero {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hfx : X.fj la ξ ν P x ≠ 0) :
    ∃ y ∈ X.FramesOverBasis ξ, X.fj la ξ ν P y ≠ 0 := by
  have hV : X.IsIsoV (X.embV ξ) := _root_.PI.FdFjNearSup.W.isIsoV_embV X hξ
  have hM := fun s => _root_.ReciprocityTheory.ChartRestriction.G.FD.flowDomainCriterion_holds r X (X.embV ξ) hV x hx s
  set tt : X.Ψ → ℝ := fun τ => X.ttV (X.embV ξ) x τ with htt
  have htt_pos : ∀ τ, 0 < tt τ := by
    intro τ
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.d4l4_c_pos X τ
    have hm := X.maj_pos hx τ (hV τ).2
    simp only [htt, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.ttV]
    positivity
  set a : X.Ψ → ℝ := fun τ => 1 - tt τ with ha
  set U : Set (X.Ψ → ℂ) := {s | X.flow ξ s x ∈ X.dom} with hUdef
  have hUeq : U = {s | ∀ τ, 0 < 1 + (s τ).im / tt τ} := by
    ext s; exact (hM s).1
  have hU : IsOpen U := by
    rw [hUeq]
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun τ => isOpen_lt continuous_const (by fun_prop)
  set F : (X.Ψ → ℂ) → ℂ := fun s => X.fj la ξ ν P (X.flow ξ s x) *
      Complex.exp (-(4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ)) with hFdef
  have hFd : DifferentiableOn ℂ F U := by
    refine DifferentiableOn.mul ?_ ?_
    · exact (_root_.ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn X la P hP hξ ν).comp (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.flow_differentiable X ξ x).differentiableOn (fun s hs => hs)
    · exact Differentiable.differentiableOn (by fun_prop)
  have hreal : ∀ s ∈ U, ∀ t : X.Ψ → ℝ, F (s + fun i => (t i : ℂ)) = F s := by
    intro s hs t
    have hfl : X.flow ξ (s + fun i => (t i : ℂ)) x
        = X.flow ξ (fun i => (t i : ℂ)) (X.flow ξ s x) := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flow_flow X hξ.2.1, add_comm]
    simp only [hFdef, hfl, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hP.1 hP.2 _ hs t]
    rw [mul_comm (Complex.exp _) (X.fj la ξ ν P (X.flow ξ s x)), mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hseg : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((u : ℂ) • fun i => I * (a i : ℂ)) ∈ U := by
    intro u hu0 hu1
    rw [hUeq]
    intro τ
    have ht := htt_pos τ
    have him : (((u : ℂ) • fun i => I * (a i : ℂ)) τ).im = u * a τ := by simp
    rw [him]
    have hq : 1 + u * a τ / tt τ = ((1 - u) * tt τ + u) / tt τ := by
      simp only [ha]; field_simp; ring
    rw [hq]
    apply div_pos _ ht
    rcases eq_or_lt_of_le hu0 with h | h
    · subst h; simpa using ht
    · nlinarith
  have hconst := eq_at_imag_of_real_translation_invariant F U hU hFd hreal a hseg
  set v : X.Ψ → ℂ := fun i => I * (a i : ℂ) with hvdef
  have hvU : v ∈ U := by simpa using hseg 1 zero_le_one le_rfl
  refine ⟨X.flow ξ v x, ⟨hvU, fun τ => ?_⟩, ?_⟩
  · have h2 := (hM v).2 hvU τ
    have hv : (v τ).im = a τ := by simp [hvdef]
    rw [hv] at h2
    have h3 : X.ttV (X.embV ξ) (X.flowV (X.embV ξ) v x) τ = 1 := by
      rw [h2]; simp [ha, htt]
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.ttV, one_div, inv_eq_one] at h3
    exact h3
  · intro h0
    have hF0 : F 0 = X.fj la ξ ν P x := by
      have := _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hP.1 hP.2 x hx 0
      simp only [hFdef]
      have h' : X.flow ξ 0 x = X.flow ξ (fun _ => 0) x := rfl
      rw [h']
      simpa using this
    have hFv : F v = 0 := by
      simp only [hFdef]
      rw [h0, zero_mul]
    rw [hconst, hF0] at hFv
    exact hfx hFv

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_mem_D1set_sSup_hatN_lt_two_mul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hfx : X.fj la ξ ν P x ≠ 0) :
    ∃ z0 ∈ X.FramesOverBasis ξ, sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}
      < 2 * X.hatN la (X.fj la ξ ν P) z0 := by
  obtain ⟨C, hC⟩ := hP.2
  have hB : ∀ y ∈ X.dom, X.pnorm la (X.fj la ξ ν P) y ≤ C :=
    fun y hy => _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.fj_bound X la P C hC hξ ν hy
  have hC0 : 0 ≤ C := (X.pointNorm_nonneg la _ x).trans (hB x hx)
  have hle : ∀ y, X.hatN la (X.fj la ξ ν P) y ≤ C := by
    intro y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hatN
    apply Real.sSup_le _ hC0
    rintro t ⟨x', hx', -, rfl⟩
    exact hB x' hx'
  have hge : ∀ y ∈ X.dom, X.pnorm la (X.fj la ξ ν P) y ≤ X.hatN la (X.fj la ξ ν P) y := by
    intro y hy
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hatN
    apply le_csSup
    · refine ⟨C, ?_⟩
      rintro t ⟨x', hx', -, rfl⟩
      exact hB x' hx'
    · exact ⟨y, hy, fun τ => rfl, rfl⟩
  obtain ⟨y, hy, hfy⟩ := exists_mem_D1set_fj_ne_zero X la P ⟨hP.1, C, hC⟩ hξ ν hx hfx
  set S := {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} with hS
  have hSb : BddAbove S := ⟨C, by rintro t ⟨y, -, rfl⟩; exact hle y⟩
  have hpos : 0 < X.hatN la (X.fj la ξ ν P) y := by
    refine lt_of_lt_of_le ?_ (hge y hy.1)
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq]
    exact mul_pos (norm_pos_iff.2 hfy) (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos X hy.1 la)
  have hyS : X.hatN la (X.fj la ξ ν P) y ∈ S := ⟨y, hy, rfl⟩
  have hM : 0 < sSup S := lt_of_lt_of_le hpos (le_csSup hSb hyS)
  obtain ⟨t, ⟨z0, hz0, rfl⟩, ht⟩ := exists_lt_of_lt_csSup ⟨_, hyS⟩ (half_lt_self hM)
  exact ⟨z0, hz0, by linarith⟩

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.FJDetect.exists_fj_ne_zero_at_split_point' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.DataX E r)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (c1 w : ℝ)
    (hdom : X.IsDominant la) (hc1 : 0 < c1) (hw : 1 ≤ w) (hspr : (∑ τ, X.spread la τ) ≤ w)
    (hr : (r : ℝ) ≤ w)
    (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
      Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)
    (hP : P ∈ X.SS la) (hP' : P ∉ X.SSgt la c1) :
    ∃ (ξ : Fin r → E) (ν : X.Ψ → ℝ), X.IsIso ξ ∧ ∑ τ, ν τ ≤ c1 ∧ (∀ τ, 0 ≤ ν τ) ∧
      (∃ z0, _root_.ReciprocityTheory.ChartRestriction.G.FD.ShortVectorHypotheses X la P ξ ν c1 w z0) ∧
      let ep0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.flowEpsilonBound X.g (_root_.ReciprocityTheory.ChartRestriction.G.FD.dE E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) X.NA X.NC c1 w
      let rh := _root_.ReciprocityTheory.ChartRestriction.G.FD.d6rh c1 w
      let La := _root_.ReciprocityTheory.ChartRestriction.G.FD.d6La r X.p0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.dE E) ep0 rh
      let ms := _root_.ReciprocityTheory.ChartRestriction.G.FD.frameIndexBound r (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.dE E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rdE E) X.NA X.NC ep0
      ∀ n' : ℕ, 1000 * ms / rh ≤ n' →
      ∃ x ∈ X.dom, ∃ lam : Fin (r - 2) → Fin r → E,
        (∀ j, lam j ∈ X.L' ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) ξ = 0) ∧
        LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
        (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
          _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧
        (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 →
          (∀ τ : X.Ψ, 0 < (τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧
          X.Jz x (X.ucomp x ξ (X.embV (lam j))) = I • X.ucomp x ξ (X.embV (lam j))) ∧
        (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) →
          (∀ τ : X.Ψ, (τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧
          X.Jz x (X.ucomp x ξ (X.embV (lam j))) = -(I • X.ucomp x ξ (X.embV (lam j)))) ∧
        (∀ j (τ : X.Ψ), ‖τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
        (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧
          (n' : ℂ) • X.aproj x ξ (X.embV μ) = X.embV (e • ξ)) ∧
        X.fj la ξ ν P x ≠ 0 := by
  have hnot : ∃ ξ, X.IsIso ξ ∧ ∃ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ c1 ∧
      ∃ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP' ⟨hP, fun ξ hξ ν hν x hx => h ξ hξ ν hν x hx⟩
  obtain ⟨ξ, hξ, ν, hν, x, hx, hfx⟩ := hnot
  have hbdd := hP.1
  have hνpos : ∀ τ, 0 ≤ ν τ := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd _ _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds hbdd hξ ν hx hfx
  obtain ⟨z0, hz0, hsup⟩ := exists_mem_D1set_sSup_hatN_lt_two_mul _ la P hbdd hξ ν hx hfx
  have hD4 : _root_.ReciprocityTheory.ChartRestriction.G.FD.ShortVectorHypotheses X la P ξ ν c1 w z0 :=
    ⟨hdom, hP, hξ, hc1, hν, ⟨x, hx, hfx⟩, hw, hspr, hχ, hz0, hsup⟩
  refine ⟨ξ, ν, hξ, hν, hνpos, ⟨z0, hD4⟩, ?_⟩
  exact (_root_.fd_point_assembly _root_.ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound _root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalFlagTranslate_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalChartNormControl_holds (_root_.fd_fj_near_sup _root_.ReciprocityTheory.ChartRestriction.G.FD.holomorphic_periodicity_extension _root_.ReciprocityTheory.ChartRestriction.G.FD.m3bNorm_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds) _root_.ReciprocityTheory.ChartRestriction.G.FD.schwarzLemmaBall_holds
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalShortVectorBound_of _root_.ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound _root_.GlobalTheory.CMTransference.cmApproximation_transference) _root_.ReciprocityTheory.ChartRestriction.G.FD.isotropicCoefficientSplitting_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.noShortVectorLowerBound_holds
    (_root_.fd_unip_move _root_.ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound _root_.ReciprocityTheory.ChartRestriction.G.FD.unitaryComplementMove _root_.ReciprocityTheory.ChartRestriction.G.FD.unipotent_majorant_bound _root_.ReciprocityTheory.ChartRestriction.G.FD.isotropicCoefficientSplitting_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.noShortVectorLowerBound_holds)) r X la P ξ ν c1 w z0 hD4 hr

end GlobalTheory.FJDetect
end

