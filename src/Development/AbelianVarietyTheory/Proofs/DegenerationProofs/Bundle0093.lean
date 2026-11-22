import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormCount

section Values
variable {F : Type} [CommRing F] {X Y : Scheme.{0}}

theorem valR_appLE (x : Sp F ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have hx' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [CrdCalc.valR_eq _ _ hx, CrdCalc.valR_eq _ _ hx', CrdCalc.valHom, CrdCalc.valHom,
    ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ h hx]
  rfl

theorem valR_scal {K : Type} [CommRing K] (ψ : K →+* F) (x : Sp F ⟶ Y) (q : Y ⟶ Sp K) (hq : x ≫ q = spMap ψ)
    (V : Y.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ V) (c : K) : valR x V (resTop V (scal q c)) = ψ c := by
  have e : valR x V (resTop V (scal q c)) =
      valR (x ≫ q) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
    valR_appLE x q ⊤ V le_top _ hx
  have e' := (CrdCalc.valR_spMap ψ (𝟙 (Sp K)) ⊤ le_rfl).2 ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  rw [Category.comp_id] at e'
  rw [e, hq, e', CrdCalc.valR_eq _ _ le_top]
  have h : (𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (((𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top).hom _) = c
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply c

theorem wchart_le (L : LB X) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem exists_monomial (L : LB X) (φ : Y ⟶ X) (N d : ℕ) {J : Type} [Fintype J]
    (σ : J → (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (N : ℤ))).Sec) (α : J → ℕ) (hα : ∑ i, α i = d) :
    ∃ s : (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => ((N * d : ℕ) : ℤ))).Sec,
      ∀ j, s.f j = ∏ i, (φ.appLE _ _ (wchart_le L φ j)).hom ((σ i).f j) ^ α i := by
  refine ⟨⟨fun j => ∏ i, (φ.appLE _ _ (wchart_le L φ j)).hom ((σ i).f j) ^ α i, fun j j' => fn_ext fun y hy => ?_⟩,
    fun _ => rfl⟩
  have v : ∀ j : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) y _ (∏ i, (φ.appLE _ _ (wchart_le L φ j)).hom ((σ i).f j) ^ α i) =
        ∏ i, gs (𝟙 Y ≫ φ) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) ((σ i).f j) ^ α i := fun j hj => by
    rw [gs_eq (𝟙 Y) y _ hj, map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_pow, ← gs_eq (𝟙 Y) y _ hj]
    exact congrArg (· ^ α i) ((gs_res (𝟙 Y) y (wchart_le L φ j) hj _).trans
      (gs_pull (𝟙 Y) φ y _ (wchart_le L φ j hj) _))
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  simp only [fun i => sec_trans (σ i) (𝟙 Y ≫ φ) y (wchart_le L φ j hy.1) (wchart_le L φ j' hy.2), mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα]
  simp only [trF]
  rw [Fin.prod_univ_one, Fin.prod_univ_one, Category.comp_id, zpow_natCast, zpow_natCast, pow_mul]
  simp only [Units.val_pow_eq_pow_val]

end Values

theorem hilb_le {k J : Type} [Field k] [Fintype J] (C : Set (J → k)) (d m : ℕ) (β : Fin m → C → k)
    (h : ∀ α : J → ℕ, ∑ i, α i = d → ∃ c : Fin m → k, ∀ v : C, ∏ i, v.1 i ^ α i = ∑ l, c l * β l v) :
    hilb C d ≤ m := by
  have le : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) ≤ Submodule.span k (Set.range β) := by
    rintro _ ⟨P, hP, rfl⟩
    rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hd : ∑ i, α i = d := by
      have := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hP hα
      rw [this]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.1 hi).symm
    obtain ⟨c, hc⟩ := h α hd
    refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨fun l => P.coeff α * c l, funext fun v => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      MvPolynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), hc v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => _root_.mul_assoc _ _ _
  have := Module.Finite.span_of_finite k (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem dim_eq (u : ρ.UTest p y₀) : u.A.g = S.g :=
  (ReciprocityTheory.ChartRestriction.G.H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint _))).trans ρ.g_eq

theorem gPt_j (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem hilb_generic_le : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (J : Type) [Fintype J] (σ : J → (u.H S.N).Sec) (d : ℕ), 1 ≤ d → hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w} d ≤ (S.N * d) ^ S.g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u J _ σ d hd
  have hN : 1 ≤ S.N * d := by
    rw [ρ.N_eq]
    exact Nat.mul_pos (pow_pos (pow_pos ρ.n_prime.pos _) _) hd
  obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hL.1.secBaseChange u.V _ u.D u.A u.G
    u.U.toUnifPre (S.N * d) hN
  rw [← dim_eq u]
  let C := {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left,
    a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w}
  have hC : ∀ w : C, ∃ (x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V)) (l : Fin 1 → u.U.LG.L.ι)
      (c : PadicAlgCl p), x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ∧
      ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => pullback.fst u.G.hom (jK u.V)) l ∧
      ∀ i, w.1 i = c * valR (x ≫ pullback.fst _ _) _ ((σ i).f l) := by
    rintro ⟨w, a, ha, l, c, hl, hw⟩
    obtain ⟨x, rfl, hx⟩ : ∃ x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = a ∧
        x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) :=
      ⟨pullback.lift a _ (ha.trans (gPt_j u)), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    exact ⟨x, l, c, hx, fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hl hy) k, hw⟩
  choose x l c hx hl hw using hC
  refine hilb_le C d _ (fun n w => c w ^ d * valR (x w) _ ((b n).f (l w))) fun α hα => ?_
  obtain ⟨s, hs⟩ := exists_monomial u.U.LG.L (pullback.fst u.G.hom (jK u.V)) S.N d σ α hα
  obtain ⟨e, he, -⟩ := hb s
  refine ⟨fun n => algebraMap _ _ (e n), fun w => ?_⟩
  have h := congrArg (CrdCalc.valHom (x w) _ (hl w)) ((hs (l w)).symm.trans (he (l w)))
  replace h := (map_prod _ _ _).symm.trans (h.trans (map_sum _ _ _))
  simp only [hw w, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα]
  refine Eq.trans ?_ ((congrArg (c w ^ d * ·) h).trans ?_)
  · refine congrArg (c w ^ d * ·) (Finset.prod_congr rfl fun i _ => Eq.symm ((map_pow _ _ _).trans ?_))
    exact congrArg (· ^ α i) ((CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_appLE _ _ _ _ _ _ (hl w)))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Eq.trans (congrArg (c w ^ d * ·) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (CrdCalc.valR_eq _ _ (hl w) _).symm))) (mul_left_comm _ _ _)
  exact (CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_scal _ (x w) _ (hx w) _ (hl w) (e n))

end GlobalTheory.ZH.FormCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdjoin
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

section
variable (R : Type) [CommRing R] [IsDomain R] (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E]
  [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] {X : Scheme.{0}} {L : LB X}

omit [IsDomain R] in
theorem comp_jFK : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def ιE : TF (R := R) F ⟶ TF (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (comp_jFK R E F)))

omit [IsDomain R] in
theorem ι_inj : Function.Injective fun ψ : (TF (R := R) E).left ⟶ X => (ιE R E F).left ≫ ψ := by
  intro a b h
  have : Epi (ιE R E F).left := by
    show Epi (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap E F))) := inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
      ⟨fun u => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (ιE R E F).left).1 h

omit [IsDomain R] in
theorem gs_ι (z : (TF (R := R) F).left) (a : Γ(Spec (CommRingCat.of E), ⊤)) :
    gs (ιE R E F).left z ⊤ a = cst F z (algebraMap E F ((Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom a)) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap E F)) a)

omit [IsDomain R] in

theorem sec_rat (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TF (R := R) E).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = 1) :
    ∃ a : E, ∀ z J, Good L z J → sval s (ιE R E F).left z J = cst F z (algebraMap E F a) := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιE R E F).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj R E F).extend_apply]) s
  have le : (⊤ : (TF (R := R) E).left.Opens) ≤
      LB.wchart L (PEmpty.elim : PEmpty → ((TF (R := R) E).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
    (((TF (R := R) E).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι R E F]
  exact (gs_res _ z le trivial _).symm

def HE (L : LB X) (σ : CoefVal.FS R F X)
    (f : ∀ z : (TF (R := R) F).left, (((TF (R := R) F).left ⟶ X) → L.ι) → (TF (R := R) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TF (R := R) E).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιE R E F).left z J).val

variable {R E F}

theorem HE.mul {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x) (H' : HE R E F L σ' f' x') :
    HE R E F L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HE.one : HE R E F L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TF (R := R) E).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HE.congr {σ σ' : CoefVal.FS R F X} {f f'} {x : F} (H : HE R E F L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HE R E F L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HE.pow {σ : CoefVal.FS R F X} {f} {x : F} (H : HE R E F L σ f x) (n : ℕ) :
    HE R E F L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HE.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HE.ratio (hL : L.IsLB) {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x)
    (H' : HE R E F L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) :
    ∃ a : E, ∀ z J, Good L z J → cst F z x' * f z J = cst F z (x * algebraMap E F a) * f' z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, hav⟩ := sec_rat R E F hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', hσ, mul_inv_cancel])
  refine ⟨a, fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : (val t (ιE R E F).left z J).val = cst F z (algebraMap E F a) * (val t' (ιE R E F).left z J).val := by
    rw [← b, Units.val_mul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [e z J hJ, e' z J hJ, c]
  simp only [cst_eq, map_mul]
  ring

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem he_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem he_sec (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    ∃ a : E, HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) (algebraMap E F a) := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := E) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, hav⟩ := sec_rat R E F hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_he (hL : L.IsLB) {φ : K → ((TF (R := R) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιE R E F).left ≫ ψ) :
    ∃ x : F, x ≠ 0 ∧ HE R E F L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := E) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιE R E F).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  refine ⟨c, hc, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], fun z J hJ => ?_⟩
  have := e (TF (R := R) F).left (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end

theorem exists_adjoin {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (A : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType A.hom] (b : TF (R := R) F ⟶ A) :
    ∃ (T : Finset F) (b₁ : TF (R := R) (IntermediateField.adjoin (FractionRing R) (T : Set F)) ⟶ A),
      ιE R _ F ≫ b₁ = b := by
  classical
  let a : Spec (CommRingCat.of F) ⟶ A.left := b.left
  obtain ⟨B, i, _, t, ht⟩ : ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ A.left) (_ : IsOpenImmersion i)
      (t : Spec B), i t = a (IsLocalRing.closedPoint F) := by
    obtain ⟨n, t, ht⟩ := A.left.affineCover.exists_eq (a (IsLocalRing.closedPoint F))
    exact ⟨_, A.left.affineCover.f n, A.left.affineCover.map_prop n, t, ht⟩
  have hr : Set.range a ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨t, ht.trans (congrArg a (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i a hr)
  have hφa : Spec.map φ ≫ i = a := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (show Spec B ⟶ Spec (CommRingCat.of R) from i ≫ A.hom)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, Spec.map_comp]
    exact Over.w b
  let : Algebra R B := ψ.hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra R B).FG := (show Algebra.FiniteType R B from h₂).out
  let K := IntermediateField.adjoin (FractionRing R) ((s.image φ.hom : Finset F) : Set F)
  have hm : ∀ x : B, φ.hom x ∈ K := fun x => by
    have hx : x ∈ Algebra.adjoin R (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have e : φ.hom (algebraMap R B r) = algebraMap (FractionRing R) F (algebraMap R _ r) := congr($hc r)
      rw [e]; exact K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have e : (ιE R K F).left ≫ Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i = b.left := by
    refine Eq.trans ?_ hφa
    show Spec.map _ ≫ _ = _
    rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨s.image φ.hom, Over.homMk (Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i) ?_,
    Over.OverMorphism.ext e⟩
  apply ι_inj R K F
  show (ιE R K F).left ≫ _ ≫ _ = (ιE R K F).left ≫ _
  rw [← Category.assoc, e, Over.w, Over.w]

end GlobalTheory.UT.CoefField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frames_on_uniformisedModel_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∀ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, LB.Gen (LB.LinComb u.A.L (Y := (TFK (R := u.V) (PadicAlgCl p)).left) (K := Fin 1) (fun _ => (x a).left) (fun _ => 1))), rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧ ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))), ∃ t : SecA u.A (PadicAlgCl p) k, ∀ (a : S.Gam) (c : S.R), IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) → ∀ z J, Good u.A.L z J → sA t (ptSecT u.A.A (x a)).left z J = @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (cst (R := u.V) (PadicAlgCl p) z (y₀ c)) * (val (powFrame u.A.A u.A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  first | exact @GlobalTheory.exists_frames_on_fibre | exact GlobalTheory.exists_frames_on_fibre | (intros; apply GlobalTheory.exists_frames_on_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFunctionFieldOfIsDominantStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_of_isDominant' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q], ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X), Set.range pt = {genericPoint X} ∧ (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧ pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  first | exact @GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant | exact GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant | (intros; apply GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_normalised_mulByN_iso : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  first | exact @GlobalTheory.ZH.MulExtend.exists_gen_mulRel | exact GlobalTheory.ZH.MulExtend.exists_gen_mulRel | (intros; apply GlobalTheory.ZH.MulExtend.exists_gen_mulRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFibreSectionOfModelSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFibre_section_of_model_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (eta : Sp Ω ⟶ U₀.toScheme), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → (N : Set M.Z).Nonempty → eta ≫ U₀.ι = M.pt → ∃ s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R))), ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP : ρ.P.L.ι) (jL : Q.L.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → g ≫ pullback.fst _ _ = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → g ≫ pullback.snd _ _ = spMap β ≫ eta → Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL → valF q _ (s.f fun _ => jP) = valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val * valF (g ≫ Q.φ) _ (σ fun _ => jL) := by
  first | exact @GlobalTheory.ZH.GenSec.exists_generic_section | exact GlobalTheory.ZH.GenSec.exists_generic_section | (intros; apply GlobalTheory.ZH.GenSec.exists_generic_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_sections_from_integral_model : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  first | exact @GlobalTheory.ZH.IntegralCarry.exists_carry | exact GlobalTheory.ZH.IntegralCarry.exists_carry | (intros; apply GlobalTheory.ZH.IntegralCarry.exists_carry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultipleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_sections_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  first | exact @GlobalTheory.ZH.GlueTheta.exists_glue | exact GlobalTheory.ZH.GlueTheta.exists_glue | (intros; apply GlobalTheory.ZH.GlueTheta.exists_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_torsion_translate_of_section : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  first | exact @GlobalTheory.UnitTheta.exists_good_point_of_sec | exact GlobalTheory.UnitTheta.exists_good_point_of_sec | (intros; apply GlobalTheory.UnitTheta.exists_good_point_of_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomSpecOfLeRingOnStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_spec_of_le_ringOn' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  first | exact @GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | exact GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | (intros; apply GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatiosStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLB_genTriv_of_ratios' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | exact GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | (intros; apply GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullbackOfProjChartStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullback_of_projChart' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | exact GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | (intros; apply GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart <;> assumption)
end

