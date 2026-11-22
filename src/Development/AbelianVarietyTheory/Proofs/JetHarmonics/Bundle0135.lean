import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0034
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupplyExtend
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_extend :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (Pl : Type) [Fintype Pl] (Z : Finset Pl) (n m : ℕ) (big : Pl → Fin 2 → ZMod d → Prop) (rk : Pl → Fin 2 → ZMod d → ℕ) (ga : Pl → Fin 2 → ZMod d → ℕ → ℕ) (nW : ℕ) (ν : ℝ), Z.Nonempty → Supply V d Z Finset.univ n m (fun o => big o.1) (fun o => rk o.1) (fun o => ga o.1) nW ν → Supply V d Pl Z n m big rk ga nW ν := by
  intro C _ V d _ Pl _ Z n m big rk ga nW ν hZ h
  obtain ⟨I, J, fI, fJ, X, F, h1, h2, h3⟩ := h
  obtain ⟨z0, hz0⟩ := hZ
  obtain ⟨q, hq⟩ : ∃ q : Pl → Z, ∀ o : Z, q o.1 = o :=
    ⟨fun o => if h : o ∈ Z then ⟨o, h⟩ else ⟨z0, hz0⟩, fun o => by simp [o.2]⟩
  refine ⟨fun o => I (q o), fun o => J (q o), fun o => fI (q o), fun o => fJ (q o), fun o => X (q o),
    fun o => F (q o), fun o => h1 (q o), ?_, ?_⟩
  · intro o ho g s
    have e := h2 (q o) (Finset.mem_univ _) g s
    have e' : (q o).1 = o := congrArg Subtype.val (hq ⟨o, ho⟩)
    simp only [e'] at e
    exact e
  · intro L hA hR hW
    have key := h3 (fun o => L o.1) ?_ ?_ ?_
    · rw [← Finset.sum_coe_sort Z]
      exact key
    · intro o _ p hp
      have e := hA o.1 o.2 p hp
      have gen : ∀ o' : Z, o' = o → p.1.Attains (X o') (F o') p.2 → p.1.Attains (X o) (F o) p.2 := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e
    · rw [← Finset.sum_coe_sort Z] at hR
      refine le_trans (le_of_eq ?_) hR
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [(h1 _).1]
    · intro o _ g a k
      have e := hW o.1 o.2 g a k
      have gen : ∀ o' : Z, o' = o → ((L o.1).map fun p => p.1.wt (X o') g a k).sum = ga o.1 g a k →
          ((L o.1).map fun p => p.1.wt (X o) g a k).sum = ga o.1 g a k := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e

end GlobalTheory.RowAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCastProdAlong
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermRatio
open GlobalTheory.BoxFamily GlobalTheory.PowGerm.FrameN

theorem clause_along {X' Y Y₁ Z : Scheme.{0}} {M' : LB X'} (g : Y₁ ⟶ X') (z : Y ⟶ Y₁) (q : ℤ)
    (σ : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => g) (fun _ => q))) (a : Γ(Y, ⊤))
    (τ : LB.Gen (LB.LinComb M' (K := PUnit.{1}) (fun _ => z ≫ g) (fun _ => q)))
    (H : ∀ j : Fin 1 → M'.ι, (Y.presheaf.map (homOfLE (ExpBijectiveUniformisation.wchart_comp_le M' g z j)).op).hom ((z.app _).hom (σ.f j)) =
      (Y.presheaf.map (homOfLE le_top).op).hom a * (τ.s (fun _ => j 0)).val) (r : Z ⟶ Y) (y : Z) (J) (hJ : Good M' y J) :
    sval σ (r ≫ z) y J = gs r y ⊤ a * (val τ r y J).val := by
  have hy : r y ∈ LB.wchart M' (fun _ : PUnit.{1} => z ≫ g) (fun _ => J (r ≫ z ≫ g)) := hJ.mem _ r
  have e := congrArg (gs r y _) (H (fun _ => J (r ≫ z ≫ g)))
  rw [sval_of σ (r ≫ z) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc])]
  exact ((gs_res _ y _ hy _).trans (gs_pull r z y _ (ExpBijectiveUniformisation.wchart_comp_le M' g z (fun _ => J (r ≫ z ≫ g)) hy) _)).symm.trans
    (e.trans ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hy _) (gs_unit _ y _ hy _))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]

theorem val_cast_prod_along (t : SAB H (Sp V)) {n : ℕ}
    (L : LB t.G.left) (h : t.PP.L = L) {Y Y₀ Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y₀ ⟶ t.G.left)) (ε : K → ℤ)
    (e : LB.Gen (LB.LinComb t.PP.L φ ε)) (q : ℕ) (r : Fin n → (Y ⟶ Y₀)) (ρ : Z ⟶ Y) (y : Z) (J) (hJ : Good L y J) :
    val (genCast h _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i))) ρ y J = ∏ i, val (genCast h _ _ e) (ρ ≫ r i) y J ^ q := by
  subst h
  show val (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i)) ρ y J = ∏ i, val e (ρ ≫ r i) y J ^ q
  rw [val_finProd _ _ _ _ _ hJ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [val_pull hJ, GermD.val_genPowG]

theorem val_eL_ratio {t : SAB H (Sp V)} {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {FT : Fin d → PS V 2 d}
    {act : 𝓞 E → Fin d → PS V 1 d} {tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)} {uv : Fin d → Fin d → V}
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (wP : PrimTyG t) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m)
    (m : ℕ) (U : (Jet V (Fin 2 × Fin d) m)ˣ)
    (hU : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (e (m + 1))
      (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left) (scaleGenG t _ _ (unitΓ U) (e m)))
    (L : LB t.G.left) (h : t.PP.L = L) {Z : Scheme.{0}} (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 1).left) (y : Z) (J)
    (hJ : Good L y J) :
    val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP (m + 1))) (r ≫ (GermD.ρT (𝟙 (Sp V)) d m).left) y J =
      gm (r ≫ (homAt (𝟙 (Sp V)) (GermD.sL m (act H.w0))).left) y ⊤ (unitΓ U) *
        val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) r y J := by
  subst h
  have hx : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (x (m + 1)).left = (x m).left := by
    rw [← Over.comp_left, hch.trunc m]
  have hs : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (homAt (𝟙 (Sp V)) (GermD.sL (m + 1) (act H.w0))).left =
      (homAt (𝟙 (Sp V)) (GermD.sL m (act H.w0))).left ≫
        (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, GermD.homAt_comp, GermD.homAt_comp, GermD.sL_trunc]
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (val_mul hJ _ _ _).symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (val_pull hJ wP _ _).trans ((congrArg (fun s => val wP s y J)
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) hx))).trans (val_pull hJ wP _ _).symm)
  · exact (val_pull hJ (e (m + 1)) _ _).trans ((congrArg (fun s => val (e (m + 1)) s y J)
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans (Category.assoc _ _ _).symm))).trans
      ((val_pull hJ (e (m + 1)) _ _).symm.trans ((val_corr hJ hU _).trans
        ((GermB.val_scale t _ _ _ _ _ y J hJ).trans (congrArg (_ * ·) (val_pull hJ (e m) _ _).symm)))))

theorem trunc_jcN (F : Type) [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    spMap ((jetTrunc : Jet F (Fin n × Fin d) (m + 1) →ₐ[F] Jet F (Fin n × Fin d) m) :
        Jet F (Fin n × Fin d) (m + 1) →+* Jet F (Fin n × Fin d) m) ≫ jcN V F d n (m + 1) i =
      jcN V F d n m i ≫ (GermD.ρT (𝟙 (Sp V)) d m).left := by
  rw [← coef_cpy, ← coef_cpy, ← Category.assoc, GermBasic.spMap_comp_eq, JetTr.jetCoef_trunc,
    ← GermBasic.spMap_comp_eq, Category.assoc, trunc_cpy, Category.assoc]
  rfl

theorem cst_prod_pow {A : Type} [CommRing A] {Z : Scheme.{0}} (r : Z ⟶ Sp A) (y : Z) {n : ℕ} (a : Fin n → A) (q : ℕ) :
    cst r y (∏ i, a i ^ q) = ∏ i, cst r y (a i) ^ q := by
  simp only [cst, gs_eq r y ⊤ trivial, map_prod, map_pow]

section Germ

variable [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} {P : PELUnif I t} {d : ℕ}
  {xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → PS V 1 d} {eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m} {wPT : PrimTyG t}
  {n : ℕ} {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)}
  [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} {pG : IsPowGrp G' t.G n}
  {U' : Unif I D' A' G'} {PU : UnifPowOf pD pA pG U' P.U}
  {F : Type} [Field F] [Algebra (FractionRing V) F] [Algebra V F] {q : ℕ} {σ' : U'.toUnifPre.SecGF F q} {f : PS F n d}

theorem val_of_germ (h : IsGermN P xT act eT wPT pG PU F q σ' f) (m : ℕ) :
    ∃ z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left,
      z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
        spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
      (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet F (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J → Good U'.LG.L y J' →
        (om (pr := fun i => (pG.pr i).left) PU.wL y J J' ((r ≫ z) ≫ UnifPre.gFK (R := V) (G := G') F) ^ q).val *
          sval σ' (r ≫ z) y J' =
          cst r y (psJet m f) * (∏ i, val (genCast (congrArg RigLB.L P.bundle).symm _ _
            (eLG t (𝟙 (Sp V)) d xT act eT wPT m)) (r ≫ jcN V F d n m i) y J ^ q).val := by
  obtain ⟨z, τ, b, h₀, h₁, h₂, h₃, h₄⟩ := h m
  refine ⟨z, h₀, h₁, fun Z r y J J' hJ hJ' => ?_⟩
  have e₁ := mapsAt_val (pr := fun i => (pG.pr i).left) PU.wL _ _ τ b h₂ r y hJ hJ'
  have e₂ := (val_corr hJ ((corr_genCast _ _ _).1 h₃) r).trans (val_cast_prod_along t _ _ _ _ _ q _ r y J hJ)
  rw [clause_along _ z _ σ' _ τ h₄ r y J' hJ', mul_left_comm, e₂.symm.trans e₁, Category.assoc, zpow_natCast,
    Units.val_mul]
  rfl

omit [IsCommMonObj G'] in
theorem gFK_hom : UnifPre.gFK (R := V) (G := G') F ≫ G'.hom =
    (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left ≫
      (TFK (R := V) F).hom ≫ jK V := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, Over.w]
  exact congrArg (· ≫ jK V) (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G')))

end Germ

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (t : SAB H (Sp V)) (P : PELUnif I t) (d n : ℕ) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V), IsChartG t (𝟙 (Sp V)) d FT act tg uv xT → ∀ (wPT : PrimTyG t), IsPrimG t wPT → ∀ (D' : DegData V I) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif I D' A' G') (PU : UnifPowOf pD pA pG U' P.U) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n d) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m), (∀ m, (eT m).IsGen) → IsGermN P xT act eT wPT pG PU F q σ' h → ∀ (m : ℕ) (U : (Jet V (Fin 2 × Fin d) m)ˣ), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (eT (m + 1)) (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left) (scaleGenG t _ _ (unitΓ U) (eT m)) → psJet m h * ∏ i : Fin n, (jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) (jetCoef (algebraMap V F) (Fin 1 × Fin d) m (jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))) ^ q = psJet m h := by
  intro E _ _ _ H V _ _ I t P d n xT FT act tg uv hch wPT _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ q σ' h eT _ hg m U hU
  obtain ⟨z₁, a₁, b₁, c₁⟩ := val_of_germ hg (m + 1)
  obtain ⟨z₀, a₀, b₀, c₀⟩ := val_of_germ hg m
  let ρ := spMap ((jetTrunc : Jet F (Fin n × Fin d) (m + 1) →ₐ[F] Jet F (Fin n × Fin d) m) :
        Jet F (Fin n × Fin d) (m + 1) →+* Jet F (Fin n × Fin d) m)
  have hf : (ρ ≫ z₁) ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      (𝟙 _ ≫ z₀) ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left := by
    rw [Category.assoc, a₁, Category.id_comp, a₀]
    exact spMap_comp_alg _
  have hz : ρ ≫ z₁ = 𝟙 _ ≫ z₀ := by
    refine GermBasic.gf_ext hf (pow_ext pG _ _ ?_ fun i => ?_)
    · rw [Category.assoc, Category.assoc _ (UnifPre.gFK (R := V) (G := G') F), gFK_hom, ← Category.assoc, hf,
        Category.assoc]
    · have hx : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (xT (m + 1)).left = (xT m).left := by
        rw [← Over.comp_left, hch.trunc m]
      rw [Category.id_comp, Category.assoc, Category.assoc, b₁, Category.assoc, b₀, jptN, jptN, ← Category.assoc,
        trunc_jcN, Category.assoc, hx]
  refine H1.cst_ext fun y => ?_
  obtain ⟨J, hJ⟩ := exists_good_at P.U.LG.isLB y
  obtain ⟨J', hJ'⟩ := exists_good_at U'.LG.isLB y
  have e₁ := c₁ _ ρ y J J' hJ hJ'
  have e₀ := c₀ _ (𝟙 _) y J J' hJ hJ'
  rw [hz, e₀] at e₁
  have k : cst ρ y (psJet (m + 1) h) = cst (𝟙 _) y (psJet m h) :=
    (H1.gs_spec _ y _).trans (congrArg (cst (𝟙 _) y) (FrRatio.psJet_trunc m h))
  have l := fun i => (congrArg (fun s => val (genCast (congrArg RigLB.L P.bundle).symm _ _
      (eLG t (𝟙 (Sp V)) d xT act eT wPT (m + 1))) s y J) (trunc_jcN F d n m i)).trans
    (val_eL_ratio hch wPT eT m U hU _ (congrArg RigLB.L P.bundle).symm (jcN V F d n m i) y J hJ)
  rw [k, Finset.prod_congr rfl fun i _ => congrArg (· ^ q) (l i)] at e₁
  simp only [Category.id_comp, mul_pow, Finset.prod_mul_distrib, Units.val_mul, ← _root_.mul_assoc] at e₁
  refine Eq.trans ?_ ((Units.mul_left_inj _).1 e₁).symm
  rw [H1.cst_mul, cst_prod_pow, Units.coe_prod]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun i _ => ?_)
  rw [Units.val_pow_eq_pow_val]
  refine congrArg (· ^ q) (Eq.trans ?_ (gs_unit _ y ⊤ trivial _))
  exact ((ExpansionValueZero.cst_comp (jcN V F d n m i) _ y _).trans (H1.gs_spec _ y _)).symm

end GlobalTheory.GermRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VanishAbstract
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.ZetaVanish

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma isUnit_det_of_mem_Glev {k r : ℕ} {g : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hg : g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) : IsUnit (Matrix.det g) := by
  have h1 : Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r := hg.1
  have h2 : (_root_.Formalism.QuantumDeterminants.Hpk k r * Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r) * g = 1 := by
    calc (_root_.Formalism.QuantumDeterminants.Hpk k r * Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r) * g
        = _root_.Formalism.QuantumDeterminants.Hpk k r * (Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  exact Matrix.isUnit_det_of_left_inverse h2

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma haar_isOpen_ne_zero_of_mem_Glev {k r : ℕ} {μ : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)}
    (hμ : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) μ) {V : Set (_root_.Formalism.QuantumDeterminants.Mt k r)} (hV : IsOpen V)
    {g₀ : _root_.Formalism.QuantumDeterminants.Mt k r} (hg₀ : Matrix.of g₀ ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) (hgV : g₀ ∈ V) :
    μ V ≠ 0 := by
  intro h0
  have hnull : ∀ a ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r), μ (_root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V) = 0 := by
    intro a ha
    rw [← Measure.map_apply (_root_.Formalism.FourierDecayAlt.P.B2x5.measurable_lmulM a) hV.measurableSet, hμ.left a ha, h0]
  obtain ⟨t, hts, htc, hteq⟩ := TopologicalSpace.isOpen_biUnion_countable
    (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) (fun a ↦ _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V)
    (fun a _ ↦ hV.preimage (_root_.Formalism.QuantumDeterminants.BesselUnitaryEquiv.continuous_lmulM a))
  have hU : μ (⋃ a ∈ t, _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V) = 0 :=
    (measure_biUnion_null_iff htc).2 fun a ha ↦ hnull a (hts ha)
  rw [hteq] at hU
  have hae : ∀ᵐ y ∂μ, y ∉ ⋃ a ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r), _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V :=
    measure_eq_zero_iff_ae_notMem.1 hU
  have hfalse : ∀ᵐ _y ∂μ, False := by
    filter_upwards [hae, _root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy hyU
    apply hy
    refine Set.mem_iUnion₂.2 ⟨Matrix.of g₀ * (Matrix.of y)⁻¹,
      _root_.Formalism.FourierDecayAlt.P.Qx3.glev_mul hg₀ (_root_.Formalism.FourierDecayAlt.Q.TInvW.glev_inv hyU), ?_⟩
    show _root_.Formalism.QuantumDeterminants.lmulM _ y ∈ V
    unfold _root_.Formalism.QuantumDeterminants.lmulM
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_Glev hyU), Matrix.mul_one]
    exact hgV
  exact hμ.ne_zero (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse))

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma zetaFunction_vanish_of_orthogonal_bumps_lemma {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hz' : _root_.Formalism.QuantumDeterminants.inWb k r z') (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z) (hT' : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z')
    (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (c : Fin r → ℂ) (h : _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ)
    (hμ : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) μ)
    (hcont : ContinuousOn h {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z'})
    (hfib : ∀ g g', (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' → (c, g') ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' →
      _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g = _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g' → h g = h g')
    (horth : ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ {ζ | _root_.Formalism.QuantumDeterminants.Tz k r z * _root_.Formalism.QuantumDeterminants.Tz k r z' < Complex.normSq ζ} →
      ∫ y : _root_.Formalism.QuantumDeterminants.Mt k r, ((φ (_root_.Formalism.FourierDecayAlt.P5.zeta k r z z' (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) ∂μ = 0)
    (g₀ : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (hg₀ : (c, g₀) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z') : h g₀ = 0 := by
  set TT := _root_.Formalism.QuantumDeterminants.Tz k r z * _root_.Formalism.QuantumDeterminants.Tz k r z' with hTT
  set ζf : _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ := _root_.Formalism.FourierDecayAlt.Q.zetaL k r z z' (Fin.last r) with hζf
  have hζc : Continuous ζf := (_root_.Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff k r z z' (Fin.last r)).continuous
  have hzeta : ∀ g, _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g = ζf g := fun g ↦ rfl
  have hH : ∀ g, _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g = Complex.normSq (ζf g) - TT := fun g ↦ rfl
  have hD : ∀ g, (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' ↔
      c ∈ _root_.Formalism.QuantumDeterminants.OmX r ∧ g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) ∧ 0 < _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g := fun g ↦ Iff.rfl
  obtain ⟨hc, hg₀G, hg₀H⟩ := (hD g₀).1 hg₀
  by_contra hw
  set w := h g₀ with hwdef
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ζ₀ := ζf g₀ with hζ₀
  set ε := (Complex.normSq ζ₀ - TT) / 2 with hε
  have hg₀H' : 0 < Complex.normSq ζ₀ - TT := by rw [hζ₀, ← hH]; exact hg₀H
  have hεpos : 0 < ε := by rw [hε]; linarith
  set R := ‖ζ₀‖ + 1 with hR
  set K := {g | g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) ∧ ε ≤ _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g ∧ ‖ζf g‖ ≤ R} with hKdef
  have hK : IsCompact K := _root_.Formalism.FourierDecayAlt.P5.HerB.isCompact_zeta_le z z' hz hz' hT hT' ε R
  have hKD : K ⊆ {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z'} := fun g hg ↦
    (hD g).2 ⟨hc, hg.1, lt_of_lt_of_le hεpos hg.2.1⟩
  set K' := K ∩ h ⁻¹' {x | ‖w‖ / 2 ≤ ‖x - w‖} with hK'def
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    ((hcont.mono hKD).preimage_isClosed_of_isClosed hK.isClosed
      (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right w))))
    Set.inter_subset_left
  have hCc : IsCompact (ζf '' K') := hK'c.image hζc
  have hζ₀C : ζ₀ ∉ ζf '' K' := by
    rintro ⟨y, ⟨hyK, hyh⟩, hy⟩
    have hyw : h y = w := hfib y g₀ (hKD hyK) hg₀ (by rw [hzeta, hzeta, hy])
    have : ‖w‖ / 2 ≤ ‖h y - w‖ := hyh
    rw [hyw, sub_self, norm_zero] at this
    linarith
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1 hCc.isClosed.isOpen_compl ζ₀ hζ₀C
  set O := {ζ : ℂ | TT + ε < Complex.normSq ζ} ∩ {ζ | ‖ζ‖ < R} with hOdef
  have hO : IsOpen O := (isOpen_lt continuous_const Complex.continuous_normSq).inter
    (isOpen_lt continuous_norm continuous_const)
  have hζ₀O : ζ₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · show TT + ε < Complex.normSq ζ₀
      rw [hε]; linarith
    · show ‖ζ₀‖ < R
      rw [hR]; linarith
  obtain ⟨ρ, hρ, hballO⟩ := Metric.isOpen_iff.1 hO ζ₀ hζ₀O
  set δ := min δ₁ ρ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hρ
  let b : ContDiffBump ζ₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hball : ∀ ζ, ζ ∈ tsupport b → ζ ∈ Metric.ball ζ₀ δ := by
    intro ζ hζ
    rw [b.tsupport_eq] at hζ
    exact Metric.closedBall_subset_ball (show δ / 2 < δ by linarith) hζ
  have hballC : Metric.ball ζ₀ δ ⊆ (ζf '' K')ᶜ :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball₁
  have hballO' : Metric.ball ζ₀ δ ⊆ O := (Metric.ball_subset_ball (min_le_right _ _)).trans hballO
  have hgood : ∀ g, g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) → b (ζf g) ≠ 0 →
      g ∈ K ∧ ‖h g - w‖ < ‖w‖ / 2 := by
    intro g hg hb
    have hmem : ζf g ∈ Metric.ball ζ₀ δ := hball _ (subset_tsupport _ hb)
    have hO' := hballO' hmem
    have h1 : TT + ε < Complex.normSq (ζf g) := hO'.1
    have h2 : ‖ζf g‖ < R := hO'.2
    have hgK : g ∈ K := ⟨hg, by rw [hH]; linarith, le_of_lt h2⟩
    refine ⟨hgK, ?_⟩
    by_contra hlt
    exact hballC hmem ⟨g, ⟨hgK, le_of_not_gt hlt⟩, rfl⟩
  have hre : ∀ g, ‖h g - w‖ < ‖w‖ / 2 → 0 < (star w * h g).re := by
    intro g hg
    have hsplit : (star w * h g).re = (star w * w).re + (star w * (h g - w)).re := by
      rw [← Complex.add_re, ← mul_add, add_sub_cancel]
    have hww : (star w * w).re = ‖w‖ ^ 2 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    have hlow : -(‖w‖ * ‖h g - w‖) ≤ (star w * (h g - w)).re := by
      have h3 := Complex.abs_re_le_norm (star w * (h g - w))
      rw [norm_mul, norm_star] at h3
      linarith [neg_abs_le (star w * (h g - w)).re]
    have h4 : ‖w‖ * ‖h g - w‖ ≤ ‖w‖ * (‖w‖ / 2) :=
      mul_le_mul_of_nonneg_left hg.le hwpos.le
    nlinarith
  have hof : Continuous (fun y : _root_.Formalism.QuantumDeterminants.Mt k r ↦ (Matrix.of y : _root_.Formalism.FourierDecayAlt.Q.Mx k r)) := continuous_id
  set F : _root_.Formalism.QuantumDeterminants.Mt k r → ℂ := fun y ↦ ((b (ζf (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) with hFdef
  have hint0 : ∫ y, F y ∂μ = 0 := horth b b.contDiff b.hasCompactSupport (fun ζ hζ ↦ by
    have h1 : TT + ε < Complex.normSq ζ := (hballO' (hball ζ hζ)).1
    show TT < Complex.normSq ζ
    linarith)
  set Kt : Set (_root_.Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ K} with hKtdef
  have hKt : IsCompact Kt := hK
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun S hS ↦ hμ.finite_compact S hS⟩
  have hFc : ContinuousOn F Kt :=
    (Complex.continuous_ofReal.comp (b.continuous.comp (hζc.comp hof))).continuousOn.mul
      ((hcont.mono hKD).comp hof.continuousOn fun y hy ↦ hy)
  have hIon : IntegrableOn F Kt μ := hFc.integrableOn_compact hKt
  have hae : F =ᵐ[μ] Kt.indicator F := by
    filter_upwards [_root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy
    by_cases hyK : y ∈ Kt
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK]
      have hb0 : b (ζf (Matrix.of y)) = 0 := by
        by_contra hb
        exact hyK (hgood _ hy hb).1
      simp [hFdef, hb0]
  have hFint : Integrable F μ :=
    ((integrable_indicator_iff hKt.measurableSet).2 hIon).congr hae.symm
  set f : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun y ↦ (star w * F y).re with hfdef
  have hfint : Integrable f μ := (hFint.const_mul (star w)).re
  have hfint0 : ∫ y, f y ∂μ = 0 := by
    have e := ContinuousLinearMap.integral_comp_comm Complex.reCLM (hFint.const_mul (star w))
    simp only [Complex.reCLM_apply] at e
    rw [hfdef, e, integral_const_mul, hint0, mul_zero, Complex.zero_re]
  have hfval : ∀ y, f y = b (ζf (Matrix.of y)) * (star w * h (Matrix.of y)).re := by
    intro y
    simp only [hfdef, hFdef]
    rw [mul_left_comm, Complex.re_ofReal_mul]
  have hfnn : 0 ≤ᵐ[μ] f := by
    filter_upwards [_root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy
    rw [Pi.zero_apply, hfval]
    by_cases hb : b (ζf (Matrix.of y)) = 0
    · rw [hb, zero_mul]
    · exact mul_nonneg (b.nonneg) (hre _ (hgood _ hy hb).2).le
  have hf0 : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hfnn hfint).1 hfint0
  set V : Set (_root_.Formalism.QuantumDeterminants.Mt k r) := {y | ζf (Matrix.of y) ∈ Metric.ball ζ₀ (δ / 4)} with hVdef
  have hVo : IsOpen V := Metric.isOpen_ball.preimage (hζc.comp hof)
  have hg₀V : (g₀ : _root_.Formalism.QuantumDeterminants.Mt k r) ∈ V := Metric.mem_ball_self (by positivity)
  refine haar_isOpen_ne_zero_of_mem_Glev hμ hVo (g₀ := g₀) hg₀G hg₀V ?_
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [hf0, _root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy0 hyG hyV
  have hb1 : b (ζf (Matrix.of y)) = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hyV)
  have hpos := hre _ (hgood _ hyG (by rw [hb1]; exact one_ne_zero)).2
  have : f y = 0 := hy0
  rw [hfval, hb1, one_mul] at this
  linarith

open MeasureTheory in

theorem _root_.GlobalTheory.HatNF.ZetaVanish.zeta_vanish : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt P.k P.r)) (c : Fin P.r → ℂ) (h : _root_.Formalism.FourierDecayAlt.Q.Mx P.k P.r → ℂ), _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev P.k P.r (Fin.last P.r)) μ → ContinuousOn h {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z'} → (∀ g g', (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → (c, g') ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → _root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' g = _root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' g' → h g = h g') → (∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {ζ | _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z * _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z' < Complex.normSq ζ} → ∫ y : _root_.Formalism.QuantumDeterminants.Mt P.k P.r, ((φ (_root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) ∂μ = 0) → ∀ g, (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → h g = 0 := by
  intro Wp Wq _ _ _ _ _ _ P Bs μ c h hμ hcont hfib horth g hg
  have hT : 0 < _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z := by
    obtain ⟨⟩ := Bs
    assumption
  have hT' : 0 < _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z' := by
    obtain ⟨⟩ := Bs
    assumption
  exact zetaFunction_vanish_of_orthogonal_bumps_lemma Bs.z_mem Bs.z'_mem hT hT' μ c h hμ hcont hfib horth g hg

end GlobalTheory.HatNF.ZetaVanish
end

