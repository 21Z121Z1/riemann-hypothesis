import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0149
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowModel

variable {C : Type*} [Category C] {J : Type*}

theorem isIso_of_prod {X Y Z : C} {p : J → (X ⟶ Z)} {r : J → (Y ⟶ Z)}
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a)
    (hY : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ Y, ∀ a, x ≫ r a = y a)
    (f : X ⟶ Y) (hf : ∀ a, f ≫ r a = p a) : IsIso f := by
  obtain ⟨g, hg, -⟩ := hX Y r
  refine ⟨g, ?_, ?_⟩
  · exact (hX X p).unique (fun a => by rw [Category.assoc, hg, hf]) (fun a => Category.id_comp _)
  · exact (hY Y r).unique (fun a => by rw [Category.assoc, hf, hg]) (fun a => Category.id_comp _)

theorem prod_precomp {X X' Z : C} {p : J → (X ⟶ Z)} (e : X' ≅ X)
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X', ∀ a, x ≫ (e.hom ≫ p a) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T y
  refine ⟨x ≫ e.inv, fun a => by rw [Category.assoc, Iso.inv_hom_id_assoc, hx], fun x' hx' => ?_⟩
  rw [← hu (x' ≫ e.hom) (fun a => by rw [Category.assoc, hx']), Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem prod_postcomp {X Z Z' : C} {p : J → (X ⟶ Z)} (e : Z ≅ Z')
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z')), ∃! x : T ⟶ X, ∀ a, x ≫ (p a ≫ e.hom) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T (fun a => y a ≫ e.inv)
  refine ⟨x, fun a => by rw [← Category.assoc, hx, Category.assoc, Iso.inv_hom_id, Category.comp_id],
    fun x' hx' => hu x' (fun a => by rw [← hx' a, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])⟩

theorem prod_of_isLimit {X Z : C} {p : J → (X ⟶ Z)} (h : IsLimit (Fan.mk X p)) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a := fun T y =>
  ⟨Fan.IsLimit.lift h y, fun a => Fan.IsLimit.fac h y a, fun x hx =>
    Fan.IsLimit.hom_ext h _ _ fun a => by
      change x ≫ p a = Fan.IsLimit.lift h y ≫ p a
      rw [hx a]; exact (Fan.IsLimit.fac h y a).symm⟩

theorem prod_pullback {S S' : Scheme.{0}} (j : S' ⟶ S) {X Z : Over S} {p : J → (X ⟶ Z)}
    (hX : ∀ (T : Over S) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : Over S') (y : J → (T ⟶ (Over.pullback j).obj Z)),
      ∃! x : T ⟶ (Over.pullback j).obj X, ∀ a, x ≫ (Over.pullback j).map (p a) = y a := by
  intro T y
  let adj := Over.mapPullbackAdj j
  obtain ⟨x, hx, hu⟩ := hX _ (fun a => (adj.homEquiv _ _).symm (y a))
  refine ⟨adj.homEquiv _ _ x, fun a => ?_, fun x' hx' => ?_⟩
  · rw [← adj.homEquiv_naturality_right, hx, Equiv.apply_symm_apply]
  · rw [← hu ((adj.homEquiv _ _).symm x') (fun a => by rw [← adj.homEquiv_naturality_right_symm, hx']),
      Equiv.apply_symm_apply]

end GlobalTheory.Poinc.Sep.PowModel

open GlobalTheory.Poinc.Sep.PowModel in

theorem GlobalTheory.Poinc.Sep.unif_pow_isPow_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hsa hα P c φc hφc pr hpr hP G _ _ hG D U
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  obtain ⟨κ, hκ, hκα⟩ := grpPullback_iso hφc hα
  haveI := U.gen_hom
  haveI := U₀.gen_hom
  have hf : ∀ u, IsMonHom (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv) := fun u => by
    haveI := hpr u
    infer_instance
  have hext : ∀ u, ∃ F : G ⟶ G₀, IsMonHom F ∧
      (Over.pullback (jK V₁)).map F = U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv := fun u => by
    haveI := hf u
    exact (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) G G₀ hG hsa (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv)).exists
  choose q hq hq' using hext
  have hcomp : ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α =
      (U.gen.hom ≫ pr u).left ≫ φc := by
    intro u
    rw [hq' u]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Over.comp_left]
    rw [hκα]
  have hsa8 : IsSemiAbelian (powObj G₀ 8) :=
    GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8) hsa
  have hPi := prod_of_isLimit (powIsLimit G₀ 8)
  obtain ⟨Q, hQ, -⟩ := hPi G q
  have hmul : ∀ (T : Over (Sp V₁)) (x y : T ⟶ G), (x * y) ≫ Q = (x ≫ Q) * (y ≫ Q) := fun T x y =>
    (hPi T fun u => (x * y) ≫ q u).unique (fun u => by rw [Category.assoc, hQ u]) (fun u => by
      haveI := hq u
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hQ u, MonObj.mul_comp])
  haveI hQm : IsMonHom Q := by
    constructor
    · have h := hmul _ (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) 1
      rw [_root_.mul_one] at h
      have h' : (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) ≫ Q = 1 := mul_eq_left.1 h.symm
      simpa [Hom.one_def] using h'
    · have h := hmul (G ⊗ G) (fst _ _) (snd _ _)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
      rw [h]; congr 1
  have hGK := prod_postcomp (κ ≪≫ U₀.gen.symm) (prod_precomp U.gen hP)
  have hPiK := prod_pullback (jK V₁) hPi
  haveI : IsIso ((Over.pullback (jK V₁)).map Q) :=
    isIso_of_prod hGK hPiK _ (fun u => by
      rw [← Functor.map_comp, hQ u, hq' u]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc])
  let e := asIso ((Over.pullback (jK V₁)).map Q)
  obtain ⟨Q', hQ'm, hQ'⟩ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) (powObj G₀ 8) G hsa8 hG e.inv).exists
  have e1 : Q ≫ Q' = 𝟙 G := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) G G hG hG (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.hom_inv_id⟩
    ⟨inferInstance, (Over.pullback _).map_id G⟩
  have e2 : Q' ≫ Q = 𝟙 _ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) (powObj G₀ 8) (powObj G₀ 8) hsa8 hsa8 (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.inv_hom_id⟩
    ⟨inferInstance, (Over.pullback _).map_id _⟩
  let E : G ≅ powObj G₀ 8 := ⟨Q, Q', e1, e2⟩
  refine ⟨q, hq, fun T' y' => ?_, hcomp⟩
  obtain ⟨x, hx, hu⟩ := prod_precomp E hPi T' y'
  exact ⟨x, fun u => by rw [← hQ u]; exact hx u, fun x' hx' => hu x' fun u => by
    change x' ≫ Q ≫ powPr G₀ u = y' u
    rw [hQ u]; exact hx' u⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactPullbackCompatibleSub
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem shortExact_pullback_cokernel_of_shortExact {C : Type*} [Category C] [Abelian C]
    {A E₂ E₃ F F' : C} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F') (hs : s ≫ ι' = ιF) (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0) (hS : (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact)
    (t : A ⟶ pullback b ι') (τ : A ⟶ F) (ht1 : t ≫ pullback.fst b ι' = f)
    (ht2 : t ≫ pullback.snd b ι' = τ ≫ s) :
    ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  have hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0 := by
    rw [← Category.assoc, ht2, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨hz', ?_⟩
  have hmf : Mono f := hS.mono_f
  have hmt : Mono t := by
    subst ht1
    exact mono_of_mono t (pullback.fst b ι')
  have hsnd : Epi (pullback.snd b ι') := Abelian.epi_pullback_of_epi_f b ι'
  refine ShortComplex.ShortExact.mk' ?_ hmt (epi_comp _ _)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  simp only at x hx
  have hc := (ShortComplex.exact_cokernel s)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hc
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ := hc (x ≫ pullback.snd b ι') (by simpa using hx)
  simp only at hy
  have hex := hS.exact
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hex
  have hb : (π₁ ≫ x ≫ pullback.fst b ι') ≫ b ≫ cokernel.π ιF = 0 := by
    have : π₁ ≫ x ≫ pullback.fst b ι' ≫ b = y ≫ ιF := by
      rw [pullback.condition, ← Category.assoc, ← Category.assoc, ← hs,
        Category.assoc π₁, hy, Category.assoc]
    have h2 := this =≫ cokernel.π ιF
    simp only [Category.assoc] at h2 ⊢
    rw [h2, cokernel.condition, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, z, hz2⟩ := hex (π₁ ≫ x ≫ pullback.fst b ι') hb
  simp only at hz2
  refine ⟨T₂, π₂ ≫ π₁, epi_comp _ _, z, ?_⟩
  simp only
  apply (cancel_mono (pullback.fst b ι')).1
  simp only [Category.assoc, ht1]
  simpa [Category.assoc] using hz2

end GlobalTheory

open GlobalTheory in
theorem GlobalTheory.shortExact_pullback_cokernel_modules : ∀ (X : Scheme.{0}) {A E₂ E₃ F F' : X.Modules} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F'), s ≫ ι' = ιF → ∀ (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0), (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact →
    ∀ (t : A ⟶ pullback b ι') (τ : A ⟶ F), t ≫ pullback.fst b ι' = f →
    t ≫ pullback.snd b ι' = τ ≫ s → ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  intro X A E₂ E₃ F F' b _ ιF ι' _ s hs f hz hS t τ ht1 ht2
  exact shortExact_pullback_cokernel_of_shortExact b ιF ι' s hs f hz hS t τ ht1 ht2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDef
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.TraitTau

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem exists_tauCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X) :
    ∃ k, Q.TauCoord a b k := by
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε), u.IsGen :=
    DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB _ _
  have hφ : lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) =
      fun k => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) k := by
    funext k
    fin_cases k
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))).symm
    · rfl
    · rfl
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))).symm
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio Q.M.isLB hφ (Q.tau a b)
    (LB.pullGen Q.M.L _ negε u (toUnit (TK R)).left) (Q.tau_gen a b) (DVR.pullGen_isGen _ _ _ _ hu _)
  let k : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom ρ
  have hk : unitOn k = ρ := Units.ext ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom_inv_id_apply ρ.val)
  refine ⟨k, u, hu, fun z J hJ => ?_⟩
  rw [hρ _ _ z J hJ, val_pull hJ, Category.id_comp, hk]

theorem isMonomialTau_ofDeg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) {m : ℕ}
    {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D t β) (hs : ∀ i y z, β i y z = β i z y)
    (ht : ∀ i, t i ≠ 0) : (Wit.ofDeg D hB).IsMonomialTau t β := by
  intro (a : D.X) (b : D.X)
  obtain ⟨k, hk⟩ := exists_tauCoord (Wit.ofDeg D hB) a b
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.RefTauCoord.main R R (Wit.ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) Function.injective_id
    (Wit.refines_ofDeg D hB) a b k hk x hx
  have hl : ∀ σ : FractionRing R →+* FractionRing R,
      (∀ r, σ (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (RingHom.id R r)) → ∀ y, σ y = y :=
    fun σ hσ => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (k := RingHom.id _) (RingHom.ext hσ))
  rw [hl _ (fun r => by rw [IsFractionRing.lift_algebraMap]; rfl)] at hu₁
  obtain ⟨_, _, -, ha⟩ := h a
  obtain ⟨_, _, -, hb⟩ := h b
  obtain ⟨_, _, -, hab⟩ := h (a + b)
  obtain ⟨u₃, hu₃⟩ := h.tau hs ht ha hb hab
  obtain ⟨xa, ha₁, ha₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D a _).1 ha
  obtain ⟨xb, hb₁, hb₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D b _).1 hb
  obtain ⟨xab, hab₁, hab₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D (a + b) _).1 hab
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.TauCoordQuot.main R D a b x xab xa xb hx hab₁ ha₁ hb₁
  rw [← ha₂, ← hb₂, ← hab₂] at hu₃
  have hc := Taut.tauCoord_mul_unit hk (u₁ * u₂⁻¹ * u₃⁻¹)
  refine ⟨k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) (u₁ * u₂⁻¹ * u₃⁻¹), ?_, hc⟩
  refine Eq.trans (b := ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) ?_ rfl
  clear hc hk hl
  have hu : ∀ u : Rˣ, algebraMap R (FractionRing R) (u : R) ≠ 0 := fun u =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero
  have e : algebraMap R (FractionRing R) u₁ * (k : FractionRing R) = algebraMap R (FractionRing R) u₂ *
      (algebraMap R (FractionRing R) u₃ * ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) := by
    rw [← hu₃, ← hu₁, hu₂, div_eq_mul_inv, mul_inv]
    ring
  have h₂ := hu u₂
  have h₃ := hu u₃
  generalize ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b = P at e ⊢
  rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp
  linear_combination e

theorem finrank_le {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (hn : 2 ≤ n) (hζ : IsUnit ζ) :
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  let K := AlgebraicClosure (FractionRing T.V)
  haveI : CharZero (FractionRing T.V) :=
    (RingHom.charZero_iff (IsFractionRing.injective T.V (FractionRing T.V))).1 inferInstance
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let κ : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap _ K)
  have hp := IsPullback.of_hasPullback F.univ.A.hom (κ ≫ T.y)
  have hq : IsPullback (T.cart.1.lift (pullback.fst F.univ.A.hom (κ ≫ T.y)) (pullback.snd F.univ.A.hom (κ ≫ T.y) ≫ κ)
      (by rw [Category.assoc]; exact hp.w)) (pullback.snd F.univ.A.hom (κ ≫ T.y)) T.A.A.hom κ :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp) (T.cart.1.lift_snd _ _ _) T.cart.1
  have hd : SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (κ ≫ T.y)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange T.A.g).of_isPullback hq T.A.smoothDim
  have e : T.A.g = g := GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (κ ≫ T.y) hd
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F), (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult).IsMonomialTau ![T.ϖ] ![T.β] ∧ (∀ a, 0 ≤ T.β a a) ∧ (∀ a, a ≠ 0 → 0 < T.β a a) ∧ (2 ≤ n → IsUnit ζ → Module.finrank ℤ T.D.toPre.X ≤ g) := by
  intro g n o _ ζ F T
  refine ⟨isMonomialTau_ofDeg _ _ T.mono (fun i => ?_) (fun i => ?_), T.mono.nonneg 0, fun a ha => ?_, finrank_le T⟩
  · fin_cases i
    exact T.symm
  · fin_cases i
    exact T.irr.ne_zero
  · obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal _).ne_top ha
    fin_cases i
    exact hi

end GlobalTheory.Poinc.TraitTau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N 0 R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f :=
    fun a c σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hpH, hpn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t htH N
  have e1 : (N : ℤ) + N * -1 = 0 := by ring
  have e2 : (0 : ℤ) + N * b = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N 0 R, f * t ^ N ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 (N * -1) (N * b) f (t ^ N) hfH hpH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hpn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    exact (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
  have hinj : Set.InjOn (fun f => f * t ^ N) (P.Bl N 0 R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) h
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N 0 R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hX P b s t hG
  have hRep : P.Rep 0 (b : ℤ) (P.A.pow b) := by
    have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A b (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
    simpa using this
  have hnef : (P.A.pow b).IsNef D := GlobalTheory.T.isNef_pow_of_isNef hAC k X p D hX P.A b hG.nef
  have hnef0 : ((P.A.pow b).shift (fun _ => (0 : ℝ)) fun _ => rfl).IsNef D :=
    GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX (P.A.pow b) 0 le_rfl hnef
  obtain ⟨Φ, hΦ⟩ := ((hAC.arExists k X p D hX).2 Unit (fun _ => P.A.pow b)).1
  have hα := ((hAC.arIso k X p D hX).2 Unit (fun _ => P.A.pow b) Φ hΦ).1 ()
  have hlim := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P 0 b (P.A.pow b) _ 0 hRep hα hnef0 3 (by norm_num)
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      P.lc ((m : ℤ) * 0) ((m : ℤ) * b) (Real.exp (3 * m)) / (m : ℝ) ^ (D + 1) < C :=
    ⟨_, hlim.eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  rw [div_lt_iff₀ hpos] at hN
  simp only [mul_zero] at hN
  refine le_trans ?_ hN.le
  exact lc_le_of_good P hG N _ (GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 _ _ hAC)

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_two_le_lc_one_add (hHS : GlobalTheory.Published.ArithHilbertSamuel) (hA : GlobalTheory.Published.ArCalc) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (b : ℕ)
    (s t : X.functionField) (hG : P.Good D b s t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  obtain ⟨h, hh⟩ := (hA.1 k X p D hX).1 P.A
  have hα : P.A.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
  have hnef := GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX P.A 0 le_rfl hG.nef
  have hrep : P.Rep 0 1 P.A := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have key := GlobalTheory.eventually_le_of_poly_asymptotics (D + 1) b
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 (j : ℤ) 2)
    (h (genericPoint X) / (D + 1).factorial) ((D + 1) * gdeg P.A D / (D + 1).factorial) (Nat.succ_pos D) hG.pos
    (fun η hη => by
      have := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hA k X p D hX P 0 1 P.A (h (genericPoint X)) 0 hrep hα hnef η hη
      simpa only [mul_zero, mul_one] using this)
    (fun η hη => by
      have h1 : ∀ᶠ j : ℕ in atTop, Real.log 2 ≤ η * j :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
      filter_upwards [h1] with j hj
      have h2 : (2 : ℝ) ≤ Real.exp (η * j) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.2 hj
      have hsub : P.Bl 0 (j : ℤ) 2 ⊆ P.Bl 0 (j : ℤ) (Real.exp (η * j)) :=
        fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h2⟩
      have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 (j : ℤ) (Real.exp (η * j)) hA
      have hle := Set.ncard_le_ncard hsub hfin
      simp only [Pair.lc]
      rcases Nat.eq_zero_or_pos (P.Bl 0 (j : ℤ) 2).ncard with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle))
    ε hε
  filter_upwards [key] with n hn
  filter_upwards [hn] with m hm
  have e1 : (((b * n + 1) * m : ℕ) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) + (m : ℤ) := by push_cast; ring
  have e2 : (((b * n * m : ℕ)) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) := by push_cast; ring
  simp only [e1, e2, zero_mul, Real.exp_zero] at hm
  exact hm

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothGroup_sections_dense_in_fibres : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := by
  first | exact @GlobalTheory.DenseSec.dense_sections | exact GlobalTheory.DenseSec.dense_sections | (intros; apply GlobalTheory.DenseSec.dense_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothNeighbourhood_translates_cover_group : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) → ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  first | exact @GlobalTheory.Mum.chart_cover | exact GlobalTheory.Mum.chart_cover | (intros; apply GlobalTheory.Mum.chart_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNoetherianPadicImageFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_noetherian_padicImage_finiteExtension : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ x ∈ U, Algebra.FiniteType ℤ Γ(X, U) → ∀ (p : ℕ) [Fact p.Prime] (φ : X.presheaf.stalk x →+* OO p), IsNoetherianRing (X.presheaf.stalk x) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ a, ((φ a : OO p) : PadicAlgCl p) ∈ K := by
  first | exact @GlobalTheory.stalk_noetherian_and_finite_image | exact GlobalTheory.stalk_noetherian_and_finite_image | (intros; apply GlobalTheory.stalk_noetherian_and_finite_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumConstantOfDeepGood
section
open GlobalTheory.CovTop GlobalTheory.BigTop Formalism.MainNotions

namespace GlobalTheory.CovTop

theorem sumC_of_deepGood : DeepGood → SumC := fun h =>
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => by
    obtain ⟨-, -, -, h4, -, h6, -, h8⟩ := h x hx hle ι p hp i hi Y hY
    exact GlobalTheory.T.sum_component_degrees_div_le_latticeSlope _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left 1 _, hi.le⟩ hY.1 hY.2.1 hY.2.2 (uM p i) h4 h6 h8⟩

end GlobalTheory.CovTop
end

