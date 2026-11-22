import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R), Function.Bijective (secTw A N σ) := by
  first | exact @GlobalTheory.Mum.Conj.secTw_bijective | exact GlobalTheory.Mum.Conj.secTw_bijective | (intros; apply GlobalTheory.Mum.Conj.secTw_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAddStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_add_chart | exact GlobalTheory.Mum.Conj.secTw_add_chart | (intros; apply GlobalTheory.Mum.Conj.secTw_add_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinearStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) → ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_chart_smul | exact GlobalTheory.Mum.Conj.secTw_chart_smul | (intros; apply GlobalTheory.Mum.Conj.secTw_chart_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), SecTw σ t (secTw A N σ t) := by
  first | exact @GlobalTheory.Mum.Conj.secTw_isTwist | exact GlobalTheory.Mum.Conj.secTw_isTwist | (intros; apply GlobalTheory.Mum.Conj.secTw_isTwist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameUniqueStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_unipotent_frame_unique : ∀ (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ), IsVB E m → ∀ (U : B.Opens) (e : Fin m → Γ(E, U)), IsFrame e → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback g).obj E) m) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (n n' : Low m → Γ(X, V)), Spans fl V (pullCol g e hV (uniR n)) → Spans fl V (pullCol g e hV (uniR n')) → n = n' := by
  first | exact @GlobalTheory.FlagCell.low_eq_of_spans_pullCol | exact GlobalTheory.FlagCell.low_eq_of_spans_pullCol | (intros; apply GlobalTheory.FlagCell.low_eq_of_spans_pullCol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrameStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (z : CxPts Y.str σ), under (ptMap σ f hf z) = f (under z) ∧ ∀ A ∈ E.S (f (under z)), ∀ B ∈ E'.S (under z), ∀ τ, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ * H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
  first | exact @GlobalTheory.ChernCalc.pullGram_eq_of_frame | exact GlobalTheory.ChernCalc.pullGram_eq_of_frame | (intros; apply GlobalTheory.ChernCalc.pullGram_eq_of_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsDiagMemMaximal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPos

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (z : Sp B) (u : Aˣ) :
    gm (spMap g) z ⊤ (unitOn u) = gm (𝟙 _) z ⊤ (unitOn (Units.map g.toMonoidHom u)) := by
  refine (congrArg (fun f => gm f z ⊤ (unitOn u)) (Category.id_comp (spMap g)).symm).trans ?_
  refine (gm_pull (𝟙 _) (spMap g) z ⊤ trivial _).symm.trans ?_
  show gm (𝟙 _) z ⊤ (Units.map (spMap g).appTop.hom (unitOn u)) = _
  congr 1
  apply Units.ext
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact e.symm

theorem gm_unitOn_injective (R : Type) [CommRing R] [IsDomain R] (z : (TK R).left) (a b : (FractionRing R)ˣ)
    (h : gm (𝟙 _) z ⊤ (unitOn a) = gm (𝟙 _) z ⊤ (unitOn b)) : a = b := by
  have e := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at e
  let φ : FractionRing R →+* (TK R).left.presheaf.stalk z :=
    ((TK R).left.presheaf.germ (𝟙 (TK R).left ⁻¹ᵁ ⊤) z trivial).hom.comp
      ((Scheme.Hom.app (𝟙 (TK R).left) ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)
  exact Units.ext (φ.injective e)

theorem gm_generic_of_closed {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)ˣ) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (h : Sp R ⟶ X) (z : (TK R).left) (hc : h (closedPoint R) ∈ U) :
    ∃ v : Rˣ, gm (jK R ≫ h) z U a =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) := by
  have htop : h ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem h hc
  have hz : h (jK R z) ∈ U := by
    show jK R z ∈ h ⁻¹ᵁ U
    rw [htop]; trivial
  let b : Γ(Sp R, ⊤)ˣ := res htop.ge (pullU h U a)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b, ?_⟩
  rw [← gm_pull (jK R) h z U hz a, ← gm_res (jK R) z htop.ge trivial (pullU h U a)]
  have hb : b = unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b) := by
    apply Units.ext
    exact ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _).symm
  change gm (jK R) z ⊤ b = _
  exact (congrArg (gm (jK R) z ⊤) hb).trans (gm_spMap_unitOn (algebraMap R (FractionRing R)) z _)

theorem exists_good_closed {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] {K : Type} (h : K → (Sp R ⟶ X)) (z : (TK R).left)
    (hinj : ∀ a b, jK R ≫ h a = jK R ≫ h b → h a = h b) :
    ∃ J, Good L z J ∧ ∀ k, h k (closedPoint R) ∈ L.U (J (jK R ≫ h k)) := by
  choose ch hch using fun g : Sp R ⟶ X => exists_chart hL (g (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => jK R ≫ h k) (fun k => ch (h k))
    (fun a b hab => by rw [hinj a b hab]) (fun k => by
      rw [Scheme.Hom.comp_apply]
      show jK R z ∈ h k ⁻¹ᵁ L.U (ch (h k))
      rw [Scheme.preimage_eq_top_of_closedPoint_mem (h k) (hch (h k))]; trivial)
  exact ⟨J, hJ, fun k => by rw [e k]; exact hch (h k)⟩

theorem ext_generic {X : Scheme.{0}} {W : Type} [CommRing W] (s : X ⟶ Sp W) [IsSeparated s] (R : Type) [CommRing R]
    [IsDomain R] (f g : Sp R ⟶ X) (h : jK R ≫ f = jK R ≫ g) : f = g := by
  have hs : f ≫ s = g ≫ s := by
    have e : jK R ≫ (f ≫ s) = jK R ≫ (g ≫ s) := by rw [← Category.assoc, h, Category.assoc]
    rw [← Spec.map_preimage (f ≫ s), ← Spec.map_preimage (g ≫ s)] at e ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at e
    congr 1
    have e' := Spec.map_injective e
    ext x
    exact IsFractionRing.injective R (FractionRing R) (congrArg (fun φ => φ.hom x) e')
  have : IsDominant (jK R) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p⟩ : Nonempty (TK R).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    let y : PrimeSpectrum R := (jK R).base p
    have hy : y.asIdeal = ⊥ := by
      ext r
      refine ⟨fun hr => ?_, fun hr => by rw [Ideal.mem_bot.1 hr]; exact zero_mem _⟩
      have h1 : algebraMap R (FractionRing R) r ∈ p.asIdeal := hr
      have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ p.isPrime
      rw [hp, Ideal.mem_bot] at h1
      exact Ideal.mem_bot.2 ((IsFractionRing.injective R (FractionRing R)).eq_iff.1 (h1.trans (map_zero _).symm))
    have hcl : closure ({y} : Set (PrimeSpectrum R)) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton, hy]; exact PrimeSpectrum.zeroLocus_bot
    have key : (x : PrimeSpectrum R) ∈ closure ({y} : Set (PrimeSpectrum R)) := hcl ▸ Set.mem_univ _
    have sub : ({y} : Set (PrimeSpectrum R)) ⊆ Set.range (jK R).base := Set.singleton_subset_iff.2 ⟨p, rfl⟩
    exact closure_mono sub key
  exact ext_of_isDominant_of_isSeparated s hs (jK R) h

theorem exists_fracMap (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁)
    (hf : Function.Injective f₁) : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ ∧
      ∀ (z : (TK V₁).left) (r : V) (k : (FractionRing V)ˣ), (k : FractionRing V) = algebraMap V _ r →
        ∃ k' : (FractionRing V₁)ˣ, (k' : FractionRing V₁) = algebraMap V₁ _ (f₁ r) ∧
          gm κK z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn k') := by
  let fK : FractionRing V →+* FractionRing V₁ := IsLocalization.map (FractionRing V₁) f₁
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f₁ hf)
  have hfK : ∀ x, fK (algebraMap V _ x) = algebraMap V₁ _ (f₁ x) := fun x => IsLocalization.map_eq _ _
  refine ⟨spMap fK, ?_, fun z r k hk => ⟨Units.map fK.toMonoidHom k, ?_, gm_spMap_unitOn fK z k⟩⟩
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hfK x
  · rw [Units.coe_map, ← hfK, ← hk]; rfl

theorem periods_pos_diag : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ hf₁ _ hloc _ _ _ _ _ x _ w₁ q _ hP a ha
  classical
  set c := e.trans e₀ with hc
  have hy : c a ≠ 0 := (AddEquiv.map_ne_zero_iff c).2 ha
  obtain ⟨r₀, hr₀, k, hk, u, hu⟩ := GlobalTheory.T.degenerationData_period_diagonal_mem_maxIdeal_mul_generator V D (c a) hy
  obtain ⟨κK, hκ, hfr⟩ := exists_fracMap V V₁ f₁ hf₁
  obtain ⟨z⟩ : Nonempty (TK V₁).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  let P : Sp V₁ ⟶ (G2 B').left := (lift (x a) (x a)).left
  have : IsProper L.T.B.hom := L.T.isAb.proper
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨J, hJ, hJc⟩ := exists_good_closed L.T.M.L L.T.M.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂' ≫ (psum L.T.B (x2 L.T.B) I.down).left)
      (fun k : Fin 4 => spMap κ₁ ≫ lamPts (L.T.c₀ ((n : ℤ) • a)) (L.T.c₀ ((n : ℤ) • a)) k)) z
    (fun _ _ h => ext_generic L.T.B.hom V₁ _ _ h)
  obtain ⟨J', hJ', hJc'⟩ := exists_good_closed D.toPre.P.L D.toPre.P.isLB V₁
    (Sum.elim (fun I : ULift (Finset (Fin 2)) => P ≫ β₂ ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)
      (fun k : Fin 4 => spMap f₁ ≫ lamPts (D.toPre.c (c a)) (D.toPre.c (c a)) k)) z
    (fun _ _ h => ext_generic D.toPre.P.A.hom V₁ _ _ h)
  have key := hP κK hκ a a z J J' hJ hJ'
  rw [hu _ κK z J' hJ'] at key
  obtain ⟨v₁, hv₁⟩ : ∃ v : V₁ˣ, val u (κK ≫ jK V) z J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    rw [hκ]
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap f₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc' (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₂, hv₂⟩ : ∃ v : V₁ˣ, isoVal w₁ (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left z J J' =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    have hp : (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x a)).left = jK V₁ ≫ P := by
      rw [← comp_lift]; rfl
    unfold isoVal
    rw [hp]
    refine gm_generic_of_closed _ _ V₁ P z ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_,
      Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => ?_⟩
    · have := hJc (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
    · have := hJc' (Sum.inl I)
      simp only [Sum.elim_inl, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨v₃, hv₃⟩ : ∃ v : V₁ˣ, val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • a)) ((TK V₁).hom ≫ spMap κ₁) z J =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v)) := by
    unfold val
    refine gm_generic_of_closed _ _ V₁ (spMap κ₁) z (Set.mem_iInter.2 fun k => ?_)
    have := hJc (Sum.inr k)
    simp only [Sum.elim_inr, Scheme.Hom.comp_apply] at this; exact this
  obtain ⟨k', hk', hkk⟩ := hfr z r₀ k hk
  rw [hkk, hv₁, hv₂, hv₃] at key
  have hmul : ∀ s t : (FractionRing V₁)ˣ,
      gm (𝟙 _) z ⊤ (unitOn (s * t)) = gm (𝟙 _) z ⊤ (unitOn s) * gm (𝟙 _) z ⊤ (unitOn t) := fun s t => by
    rw [← map_mul]; congr 1; exact map_mul _ _ _
  rw [← hmul, ← hmul, ← hmul] at key
  have e' := gm_unitOn_injective V₁ z _ _ key

  have hq : q a a = k' * Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v₁ * (v₂ * v₃)⁻¹) := by
    rw [map_mul, map_inv, map_mul]
    exact (eq_mul_inv_of_mul_eq e'.symm).trans (_root_.mul_assoc _ _ _)
  have hv : ((q a a : (FractionRing V₁)ˣ) : FractionRing V₁) = algebraMap V₁ _ (f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹)) := by
    rw [hq, Units.val_mul, hk', Units.coe_map, map_mul]
    rfl
  refine ⟨f₁ r₀ * ↑(v₁ * (v₂ * v₃)⁻¹), Ideal.mul_mem_right _ _ (map_nonunit f₁ r₀ hr₀), ?_, hv⟩
  intro hw
  apply (q a a).ne_zero
  rw [hv, hw, map_zero]

end GlobalTheory.PeriodPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.ClosFacts

theorem range_closι {X : Scheme.{0}} (z : X) : range (closι z) = closure {z} :=
  range_redι (Closeds.closure {z})

theorem isIntegral_clos {X : Scheme.{0}} (z : X) : IsIntegral (clos z) :=
  isIntegral_red (Z := Closeds.closure {z}) isIrreducible_singleton.closure

theorem clos_facts : ∀ (X : Scheme.{0}) (z : X), ∃ _ : IsIntegral (clos z), closι z (genericPoint (clos z)) = z ∧ topologicalKrullDim (clos z) = topologicalKrullDim (closure ({z} : Set X)) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = z → ∃ g : Y ⟶ clos z, g ≫ closι z = π ∧ g (genericPoint Y) = genericPoint (clos z) ∧ g.residueDegree (genericPoint Y) = π.residueDegree (genericPoint Y) ∧ (IsClosedImmersion π → IsIso g) := by
  intro X z
  have hI := isIntegral_clos z
  have hr := range_closι z
  have hi : closι z (genericPoint (clos z)) = z := by
    have h₁ := (genericPoint_spec (clos z)).image (closι z).continuous
    rw [image_univ, hr, closure_closure] at h₁
    exact h₁.eq isGenericPoint_closure
  refine ⟨hI, hi, (topologicalKrullDim_eq_of_isEmbedding (closι z).isClosedEmbedding.isEmbedding hr), ?_⟩
  intro Y _ π hπ
  have : Surjective (Limits.pullback.snd (closι z) π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr, ← hπ]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd (closι z) π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ clos z, g ≫ closι z = π :=
    ⟨inv (Limits.pullback.snd (closι z) π) ≫ Limits.pullback.fst (closι z) π, by
      rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint (clos z) :=
    (closι z).isClosedEmbedding.injective (hπ.trans hi.symm)
  refine ⟨g, rfl, hg, ?_, fun hc => ?_⟩
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion (closι z), one_mul]
  · have : IsClosedImmersion g := IsClosedImmersion.of_comp_isClosedImmersion g (closι z)
    have : Surjective g := ⟨by
      rw [← Set.range_eq_univ]
      have h₁ := (genericPoint_spec Y).image g.continuous
      rw [image_univ, g.isClosedEmbedding.isClosed_range.closure_eq, hg] at h₁
      exact h₁.def.symm.trans (genericPoint_spec (clos z)).def⟩
    exact isIso_of_isClosedImmersion_of_surjective g

end GlobalTheory.ClosFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceThetaOfCoreStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_theta_of_core : Size → RefCore → RefTheta := by
  first | exact @GlobalTheory.RefSum.refTheta_of_refCore | exact GlobalTheory.RefSum.refTheta_of_refCore | (intros; apply GlobalTheory.RefSum.refTheta_of_refCore <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PolDeg.refine_monomial_of_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R → Q.IsMonomialTau t δ → (∀ i, t i ∈ maximalIdeal R) → (∀ i, t i ≠ 0) → (∀ i y z, δ i y z = δ i z y) → (∀ i y, 0 ≤ δ i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧ IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ _ Q m t δ hCN hmono htm ht0 hsymm hnn hdef
  obtain ⟨R₁, _, _, _, ρ₁, P, β, β₂, hCN₁, hinj₁, hfin₁, hloc₁, hpb, hsq, hiso⟩ := GlobalTheory.T.exists_symmetricPolarisation_finiteExtension R Q hCN
  haveI : IsNoetherianRing R₁ := hCN₁.1
  obtain ⟨D, e, f, hD⟩ := GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function R R₁ Q ρ₁ P β β₂ hinj₁ hpb hsq hiso
  obtain ⟨hfs, hfc⟩ := GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle R R₁ Q ρ₁ D e f hinj₁ hD
  obtain ⟨g, hg⟩ := GlobalTheory.T.symmetric_twoCocycle_free_abelian_isCoboundary D.X _ f hfs hfc
  have hD₁ : Half Q ρ₁ (rescale D g) e (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₁ Q ρ₁ D e f (fun _ _ => 1) g hD (fun a b => by rw [hg a b, _root_.mul_one])
  have hb₁ : (rescale D g).TauBimult := GlobalTheory.T.tauBimult_of_refines_polarised_data R R₁ Q ρ₁ (rescale D g) e hinj₁ hD₁
  obtain ⟨h, hhom, hev⟩ := GlobalTheory.T.exists_hom_evenDefect_bimultiplicative_periods R₁ (rescale D g) hb₁
  obtain ⟨R₂, _, _, _, σ, gam, r, et, hCN₂, hinj₂, hfin₂, hloc₂, hgam, hr, hη, hη2⟩ :=
    GlobalTheory.T.exists_sqrt_latticeHom_finiteExtension_complete R₁ (rescale D g).X h m (fun i => ρ₁ (t i)) hCN₁ hhom
  haveI : IsNoetherianRing R₂ := hCN₂.1
  obtain ⟨D₂, β', v, xe, hpb', hv, hc', hrig, hpsi⟩ := GlobalTheory.T.exists_baseChange_raw_degenerationData_injective R₁ R₂ σ (rescale D g) gam hgam
  have hD₂ := GlobalTheory.T.refinesPolarisedData_baseChange_symmetric R Q R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi ρ₁ e hinj₁ hD₁
  have hev₂ := GlobalTheory.T.evenDefect_degenerationData_baseChange R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi h hev
  have hinj : Function.Injective (σ.comp ρ₁) := hinj₂.comp hinj₁
  have hηx : ∀ a b : D₂.X, et (xe (a + b)) = et (xe a) * et (xe b) := fun a b => by rw [map_add, hη]
  have hD₃ : Half Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₂ Q (σ.comp ρ₁) D₂ (xe.trans e) (fun _ _ => 1) (fun _ _ => 1) (fun χ => et (xe χ)) hD₂
      (fun a b => by rw [hηx, _root_.mul_one, mul_right_comm (et (xe a)), mul_inv_cancel, _root_.one_mul, mul_inv_cancel])
  have hev₃ : (rescale D₂ fun χ => et (xe χ)).PsiEven :=
    GlobalTheory.T.rescaleDegDataTrivialisations_psiEven_of_sqrt R₂ D₂ _ (fun χ => et (xe χ)) hev₂ hηx (fun a => hη2 (xe a))
  have hb₃ : (rescale D₂ fun χ => et (xe χ)).TauBimult :=
    GlobalTheory.T.tauBimult_of_refines_polarised_data R R₂ Q (σ.comp ρ₁) _ (xe.trans e) hinj hD₃
  have hr' : ∀ i, r i ^ 2 = (σ.comp ρ₁) (t i) := fun i => hr i
  have hmon := GlobalTheory.T.exists_monomial_trivialisation_sqrt_refinedPolarisedData R R₂ Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) m t r δ hCN₂ hinj hD₃
    hev₃ hb₃ hmono hnn ht0 hr'
  have hrm : ∀ i, r i ∈ maximalIdeal R₂ := by
    intro i
    refine (inferInstance : (maximalIdeal R₂).IsPrime).mem_of_pow_mem 2 ?_
    rw [hr' i, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).1 (htm i) ((isUnit_map_iff (σ.comp ρ₁) _).1 hu)
  have key : ∀ (D₃ : DegPre R₂) (e' : D₃.X ≃+ Q.X), D₃.PsiEven → D₃.TauBimult →
      Half Q (σ.comp ρ₁) D₃ e' (fun _ _ => 1) →
      IsMonomial D₃ r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i)) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R')
        (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
        IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧
        IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
    intro D₃ e' h1 h2 h3 h4
    obtain ⟨DD, rfl⟩ := GlobalTheory.T.degenerationData_of_monomial_even_bimultiplicative R₂ D₃ m r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i))
      h1 h2 h4 hrm (fun i y z => by simp [pull, hsymm i (e' y) (e' z)])
      (fun y hy => by
        obtain ⟨i, hi⟩ := hdef (e' y) (by simpa using hy)
        exact ⟨i, by simpa [pull] using hi⟩)
    exact ⟨R₂, inferInstance, inferInstance, inferInstance, σ.comp ρ₁, r, DD, e', hCN₂, hinj,
      hfin₂.comp hfin₁, inferInstance, hr', h3.refines, h4⟩
  exact key _ _ hev₃ hb₃ hD₃ hmon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfPeriodicRegularDifferencesRatioCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_of_periodic_regular_differences_ratio_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (h : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (h k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), h k (z + l) = h k z) → (∀ k j, IsReg u.ex (W k ⊓ W j) (h k - h j)) → ∀ k, IsReg u.ex (W k) (h k) := by
  first | exact @GlobalTheory.CechPer.isReg_of_isReg_sub | exact GlobalTheory.CechPer.isReg_of_isReg_sub | (intros; apply GlobalTheory.CechPer.isReg_of_isReg_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAffineNonzeroLocusAbelianSchemeNoetherStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_affine_nonzeroLocus_abelianScheme_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ s : LB.Sec M, IsAffineOpen (Out.nonzeroLocus s) → (∀ p : Sp R, ∃ x ∈ Out.nonzeroLocus s, A.hom x = p) → Out.RelAmple A M := by
  first | exact @GlobalTheory.AffineLocusAmple.relAmple_of_affine_nonzeroLocus | exact GlobalTheory.AffineLocusAmple.relAmple_of_affine_nonzeroLocus | (intros; apply GlobalTheory.AffineLocusAmple.relAmple_of_affine_nonzeroLocus <;> assumption)
end

