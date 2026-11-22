import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

private theorem isGrpPullback_one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (X : Over S) :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  have h1 : (toUnit X).left = X.hom := by simp
  show (toUnit X ≫ η[G]).left = _
  rw [Over.comp_left, h1]

private theorem left_comp_comp_hom_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} (y : T ⟶ G') :
    (y.left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ x)).hom := by
  simp only [Over.mk_hom, Category.assoc, h.1.w]
  rw [← Category.assoc, Over.w]

private theorem eq_one_of_left_eq_one_comp_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)}
    (u₀ : Over.mk (T.hom ≫ x) ⟶ G) (hu : u₀.left = (1 : T ⟶ G').left ≫ φ) : u₀ = 1 := by
  have h2 := h.2 T 1 1 u₀ u₀ hu hu
  rw [_root_.mul_one, ← hu] at h2
  have h3 : u₀ * u₀ = u₀ := Over.OverMorphism.ext h2
  simpa using h3

private theorem list_prod_left_comp_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G')) (u₀ : Fin m → (Over.mk (T.hom ≫ x) ⟶ G)),
      (∀ i, (u₀ i).left = (u i).left ≫ φ) → (List.ofFn u₀).prod.left = (List.ofFn u).prod.left ≫ φ := by
  intro m
  induction m with
  | zero =>
    intro u u₀ _
    simp only [List.ofFn_zero, List.prod_nil]
    have e0 : (Over.homMk ((1 : T ⟶ G').left ≫ φ) (left_comp_comp_hom_of_isGrpPullback h 1) : Over.mk (T.hom ≫ x) ⟶ G) = 1 :=
      eq_one_of_left_eq_one_comp_of_isGrpPullback h _ rfl
    rw [← e0]
    rfl
  | succ m ih =>
    intro u u₀ hu
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact h.2 T _ _ _ _ (hu 0) (ih _ _ fun i => hu i.succ)

private theorem eq_of_left_comp_eq_of_isGrpPullback' {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} {u v : T ⟶ G'}
    (e : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w, Over.w]))

private theorem spMap_fstHom_comp_epsR_hom (K : Type) [Field K] :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (epsR K).hom = 𝟙 (Sp K) := by
  have e1 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K :=
    RingHom.ext fun _ => rfl
  show Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = 𝟙 _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_id, Spec.map_id]

private theorem isLieComb_iff_eq_prodPts {K : Type} [Field K] {G' : Over (Sp K)} [GrpObj G'] {n : ℕ} (c : Fin n → K)
    (v : Fin n → (epsR K ⟶ G')) (y : epsR K ⟶ G') : IsLieComb c v y ↔ y = Chart.prodPts c v := by
  unfold IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    have e1 : u = fun i => Chart.spMap (Chart.scaleD (c i)) ≫ v i := funext fun i => Over.OverMorphism.ext (hu i)
    rw [e1]
    rfl
  · rintro rfl
    exact ⟨fun i => Chart.spMap (Chart.scaleD (c i)) ≫ v i, fun i => rfl, rfl⟩

private theorem lieMult_of_finrank_eigenSub_eq {O K : Type} [CommRing O] [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S}
    {G' : Over (Sp K)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
    {n : ℕ} {v : Fin n → (epsR K ⟶ G')} (hv : IsLieBasis v) (act : OAct O G) (act' : OAct O G')
    (ha : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (ρ : O →+* Module.End K (Fin n → K))
    (hρ : ∀ a c, Chart.prodPts (ρ a c) v = Chart.prodPts c v ≫ act'.act a) (τ : O →+* K) (N : ℕ)
    (hN : Module.finrank K (GlobalTheory.EigenSplit.eigenSub ρ τ) = N) : LieMult act x τ N := by
  have hv0 := hv
  unfold IsLieBasis at hv0
  obtain ⟨hvt, hvu⟩ := hv0
  let P : (epsR K ⟶ G') → (epsPt x ⟶ G) := fun y => Over.homMk (y.left ≫ φ) (left_comp_comp_hom_of_isGrpPullback h y)
  have hP : ∀ y, (P y).left = y.left ≫ φ := fun y => rfl
  have hU : η[G'].left ≫ φ = x ≫ η[G].left := by
    have e1 := congrArg Over.Hom.left (eq_one_of_left_eq_one_comp_of_isGrpPullback h (T := epsR K) (P 1) rfl)
    rw [hP, isGrpPullback_one_left, isGrpPullback_one_left] at e1
    simp only [Over.mk_hom, Category.assoc] at e1
    have e2 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ t) e1
    have hf1 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) :=
      spMap_fstHom_comp_epsR_hom K
    simp only [← Category.assoc, hf1, Category.id_comp] at e2
    exact e2
  have hfstw : ∀ y : epsR K ⟶ G', (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ y.left) ≫ G'.hom = 𝟙 _ := by
    intro y
    rw [Category.assoc, Over.w, spMap_fstHom_comp_epsR_hom]
  have hηw : η[G'].left ≫ G'.hom = 𝟙 _ := by
    exact Over.w η[G']
  have htan : ∀ y : epsR K ⟶ G', IsTangent y ↔
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (P y).left = (1 : Over.mk x ⟶ G).left := by
    intro y
    unfold IsTangent
    rw [hP, isGrpPullback_one_left]
    simp only [Over.mk_hom]
    constructor
    · intro hy
      rw [← Category.assoc, hy, hU]
    · intro hy
      apply h.1.hom_ext
      · rw [Category.assoc]
        exact hy.trans hU.symm
      · exact (hfstw y).trans hηw.symm
  have heig : ∀ (y : epsR K ⟶ G') (a : O) (s : K),
      (P y ≫ act.act a).left = spMap (epsScale s) ≫ (P y).left ↔ y ≫ act'.act a = Chart.spMap (Chart.scaleD s) ≫ y := by
    intro y a s
    have e1 : (P y ≫ act.act a).left = (y ≫ act'.act a).left ≫ φ := by
      simp only [Over.comp_left, Category.assoc, hP, ha]
    rw [e1, hP]
    constructor
    · intro e2
      apply eq_of_left_comp_eq_of_isGrpPullback' h
      rw [e2, Over.comp_left, Category.assoc]
      try rfl
    · intro e2
      rw [e2, Over.comp_left, Category.assoc]
      try rfl
  let B := Module.finBasisOfFinrankEq K (GlobalTheory.EigenSplit.eigenSub ρ τ) hN
  let e : Fin N → (epsR K ⟶ G') := fun i => Chart.prodPts ((B i : Fin n → K)) v
  have heS : ∀ c : Fin n → K, c ∈ GlobalTheory.EigenSplit.eigenSub ρ τ → ∀ a,
      Chart.prodPts c v ≫ act'.act a = Chart.spMap (Chart.scaleD (τ a)) ≫ Chart.prodPts c v := by
    intro c hc a
    rw [← hρ, GlobalTheory.EigenSplit.mem_eigenSub.1 hc a, GlobalTheory.LieEigen.prodPts_smul]
  have hlift : ∀ w : epsPt x ⟶ G, ∃ y, P y = w := by
    intro w
    refine ⟨Over.homMk (h.1.lift w.left (epsR K).hom (Over.w w)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _
  have hsc : ∀ (d : K) (i : Fin N),
      (P (Chart.spMap (Chart.scaleD d) ≫ e i)).left = spMap (epsScale d) ≫ (P (e i)).left := by
    intro d i
    show (Chart.spMap (Chart.scaleD d) ≫ e i).left ≫ φ = spMap (epsScale d) ≫ (e i).left ≫ φ
    rw [Over.comp_left, Category.assoc]
    try rfl
  have hprod : ∀ (d : Fin N → K) (u : Fin N → (epsPt x ⟶ G)),
      (∀ i, (u i).left = spMap (epsScale (d i)) ≫ (P (e i)).left) →
        (List.ofFn u).prod = P (Chart.prodPts (∑ i, d i • (B i : Fin n → K)) v) := by
    intro d u hu
    apply Over.OverMorphism.ext
    rw [hP, ← GlobalTheory.LieEigen.prodPts_prodPts hvt d fun i => (B i : Fin n → K)]
    exact list_prod_left_comp_of_isGrpPullback h (fun i => Chart.spMap (Chart.scaleD (d i)) ≫ e i) u
      (fun i => by rw [hu i, ← hsc]; rfl)
  unfold LieMult
  refine ⟨fun i => P (e i), fun i => ?_, fun w hw => ?_⟩
  · unfold IsLieEigen
    exact ⟨(htan (e i)).1 (GlobalTheory.LieEigen.isTangent_prodPts hvt _),
      fun a => (heig (e i) a (τ a)).2 (heS _ (B i).2 a)⟩
  · unfold IsLieEigen at hw
    obtain ⟨hw0, hw1⟩ := hw
    obtain ⟨y, rfl⟩ := hlift w
    have hty : IsTangent y := (htan y).2 hw0
    have hye : ∀ a, y ≫ act'.act a = Chart.spMap (Chart.scaleD (τ a)) ≫ y := fun a => (heig y a (τ a)).1 (hw1 a)
    obtain ⟨c, hc, -⟩ := hvu y hty
    rw [isLieComb_iff_eq_prodPts] at hc
    subst hc
    have hcm : c ∈ GlobalTheory.EigenSplit.eigenSub ρ τ := by
      rw [GlobalTheory.EigenSplit.mem_eigenSub]
      intro a
      apply GlobalTheory.LieEigen.prodPts_injective hv
      show Chart.prodPts (ρ a c) v = Chart.prodPts (τ a • c) v
      rw [hρ, hye, GlobalTheory.LieEigen.prodPts_smul]
    let cc : GlobalTheory.EigenSplit.eigenSub ρ τ := ⟨c, hcm⟩
    have key : ∀ (d : Fin N → K) (u : Fin N → (epsPt x ⟶ G)),
        (∀ i, (u i).left = spMap (epsScale (d i)) ≫ (P (e i)).left) →
          (P (Chart.prodPts c v) = (List.ofFn u).prod ↔ d = B.repr cc) := by
      intro d u hu
      rw [hprod d u hu]
      constructor
      · intro hEq
        have h1 : Chart.prodPts c v = Chart.prodPts (∑ i, d i • (B i : Fin n → K)) v :=
          eq_of_left_comp_eq_of_isGrpPullback' h (congrArg Over.Hom.left hEq)
        have h2 := GlobalTheory.LieEigen.prodPts_injective hv h1
        have h3 : cc = ∑ i, d i • B i := by
          apply Subtype.ext
          rw [Submodule.coe_sum]
          simp only [Submodule.coe_smul]
          exact h2
        rw [h3, Module.Basis.repr_sum_self]
      · intro hd
        subst hd
        have h4 := congrArg Subtype.val (B.sum_repr cc)
        rw [Submodule.coe_sum] at h4
        simp only [Submodule.coe_smul] at h4
        exact congrArg (fun t => P (Chart.prodPts t v)) h4.symm
    refine ⟨fun i => B.repr cc i, ⟨fun i => P (Chart.spMap (Chart.scaleD (B.repr cc i)) ≫ e i), fun i => hsc _ i, ?_⟩, ?_⟩
    · exact (key _ _ fun i => hsc _ i).2 rfl
    · rintro d ⟨u, hu, hEq⟩
      exact (key d u hu).1 hEq

theorem GlobalTheory.exists_lie_coordinates_lieMult_iff : ∀ (O R : Type) [CommRing O] [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR R ⟶ G)), Smooth G.hom → IsLieBasis v → ∃ M : O →+* Module.End R (Fin n → R), ∀ (K : Type) [Field K] (f : R →+* K), ∃ M' : O →+* Module.End K (Fin n → K), (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ (τ : O →+* K) (N : ℕ), LieMult act (spMap f) τ N ↔ Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = N := by
  intro O R _ _ G _ _ act n v hs hv
  obtain ⟨M, hM⟩ := GlobalTheory.LieEigen.exists_action hv act
  refine ⟨M, fun K _ f => ?_⟩
  have hpb := isGrpPullback_pullback G (spMap f)
  obtain ⟨v', hv', hvv⟩ := GlobalTheory.exists_isLieBasis_baseChange R K f G ((Over.pullback (spMap f)).obj G)
    (pullback.fst G.hom (spMap f)) hpb hs n v hv
  obtain ⟨act', hact'⟩ := GlobalTheory.DetExtend.exists_oAct_pullback (spMap f) act
  have ha : ∀ a, (act'.act a).left ≫ pullback.fst G.hom (spMap f) =
      pullback.fst G.hom (spMap f) ≫ (act.act a).left := by
    intro a
    rw [hact']
    exact pullback.lift_fst _ _ _
  obtain ⟨M', hM'⟩ := GlobalTheory.LieEigen.exists_action hv' act'
  refine ⟨M', fun a c => GlobalTheory.LieEigen.action_baseChange hpb hv' hvv ha hM hM' a c, fun τ N => ⟨fun hN => ?_, fun hN => ?_⟩⟩
  · exact GlobalTheory.LieEigen.finrank_of_lieMult hpb hv' ha hM' hN
  · exact lieMult_of_finrank_eigenSub_eq hpb hv' act act' ha M' hM' τ N hN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationLiftSmoothOverField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

noncomputable def liftConstHomK {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem liftConstHomK_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens)
    (hp : Smooth p) (hU : IsAffineOpen U) : (liftConstHomK p U).Smooth := by
  have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (fun _ _ => trivial)
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) h1

theorem app_constFn_of_commK {R S : Type} [CommRing R] [CommRing S] (x₀ : R →+* S) {Y X : Scheme.{0}}
    (q : Y ⟶ Sp S) (p : X ⟶ Sp R) (m : Y ⟶ X) (h : m ≫ p = q ≫ spMap x₀) (W : X.Opens) (a : R) :
    (m.app W).hom (constFn p W a) = constFn q (m ⁻¹ᵁ W) (x₀ a) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W =
      CommRingCat.ofHom x₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
    rw [← Category.assoc (CommRingCat.ofHom x₀), Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
    have e1 : p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W = (m ≫ p).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : (q ≫ spMap x₀).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) =
        (Spec.map (CommRingCat.ofHom x₀)).appTop ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    rw [e1, ← e2]
    simp only [h]
  exact congrArg (fun φ => φ.hom a) key

theorem exists_locDerK_of_smooth : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  intro K _ R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHomK p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHomK_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHomK q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_commK x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := GlobalTheory.T.exists_derivation_extend' R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHomK q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add])
    (fun a b => by rw [hD.2, hc, hc, map_add, map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := (GlobalTheory.T.existsUnique_localDerivationAlongFibreField_of_affine K R Y X q p m D W₀ hW).1 d₀ h1 h2 h3
  exact ⟨d, hd⟩

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPartialBundleIsoNormalised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.BundleNormalise

open GlobalTheory.RigidTriv

variable {X Y : Scheme.{0}}

private theorem gm_res_eq_gm (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V) (u : Γ(X, U)ˣ) :
    gm f y V (res h u) = gm f y U u := by
  rw [← gm_id_pull f y V hy, pullU_res₂ f h u]
  exact gm_rp₁ f y U (f ⁻¹ᵁ V) (f.preimage_mono h) hy u

theorem gm_div {M M' : LB X} (f : Y ⟶ X) (y : Y) (a a' : M.ι) (b b' : M'.ι)
    (hm : f y ∈ M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) :
    gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) ((LB.div M M').g (a, b) (a', b')) =
      gm f y _ (M.g a a') * (gm f y _ (M'.g b b'))⁻¹ := by
  simp only [LB.div]
  rw [map_mul, map_inv]
  erw [gm_res_eq_gm f y _ hm, gm_res_eq_gm f y _ hm]

theorem gm_iso {M M' : LB X} {w : LB.Iso M' M} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) (a a' : M.ι) (b b' : M'.ι)
    (hm : f y ∈ M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) :
    gm f y (M.U a ⊓ M'.U b) (w.s (a, b)) =
      gm f y _ (M.g a a') * (gm f y _ (M'.g b b'))⁻¹ * gm f y (M.U a' ⊓ M'.U b') (w.s (a', b')) := by
  have hl : M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b') ≤ M.U a ⊓ M'.U b := inf_le_left
  have hr : M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b') ≤ M.U a' ⊓ M'.U b' := inf_le_right
  refine (gm_res_eq_gm f y hl hm (w.s (a, b))).symm.trans ?_
  refine (congrArg (gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b'))) (hw (a, b) (a', b'))).trans ?_
  refine (map_mul (gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b'))) _ _).trans ?_
  exact congrArg₂ (· * ·) (gm_div f y a a' b b' hm) (gm_res_eq_gm f y hr hm (w.s (a', b')))

private theorem units_ext_of_gm_id_eq {Z : Scheme.{0}} {W : Z.Opens} (u v : Γ(Z, W)ˣ)
    (h : ∀ x ∈ W, gm (𝟙 Z) x W u = gm (𝟙 Z) x W v) : u = v := by
  have key : (Scheme.Hom.app (𝟙 Z) W).hom u.val = (Scheme.Hom.app (𝟙 Z) W).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf
    intro x hx
    have hx' : (𝟙 Z) x ∈ W := hx
    have e := congrArg Units.val (h x hx)
    simp only [gm, pullU, dif_pos hx', MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at e
    exact e
  ext1
  exact (ConcreteCategory.bijective_of_isIso (Scheme.Hom.app (𝟙 Z) W)).1 key

private theorem res_res_units' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    res h2 (res h1 u) = res (h2.trans h1) u := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

private theorem mem_pull_U_of_mem {X S : Scheme.{0}} (M : LB X) (e : S ⟶ X) (x : S) (a : M.ι) (h : e x ∈ M.U a) :
    x ∈ (M.pull e).U (fun _ => a) :=
  Set.mem_iInter.2 fun _ => h

private theorem comm_mul_mul_inv_mul_mul_inv_inv_eq {G : Type*} [CommGroup G] (g g' a a' w : G) :
    g * a * (g' * a')⁻¹ * (g * g'⁻¹ * w)⁻¹ = a * a'⁻¹ * w⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem eq_mul_mul_inv_mul_inv_mul {G : Type*} [CommGroup G] (a b w : G) : a = w * (a * b⁻¹ * w⁻¹) * b := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_iso_normalised : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V V' : S.Opens) (M M' : LB X) (r : (M.pull e).Gen) (r' : (M'.pull e).Gen), e ≫ p = 𝟙 S → ⨆ a, M.U a = p ⁻¹ᵁ V → ⨆ a, M'.U a = p ⁻¹ᵁ V' → r.IsGen → r'.IsGen → LBIso M' M → ∃ w : LB.Iso M' M, w.IsGen ∧ ∀ (x : S) (a : M.ι) (b : M'.ι), e x ∈ M.U a → e x ∈ M'.U b → gm (𝟙 S) x ((M.pull e).U fun _ => a) (r.s fun _ => a) = gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x ((M'.pull e).U fun _ => b) (r'.s fun _ => b) := by
  intro X S p e V V' M M' r r' he hV hV' hr hr' hw
  obtain ⟨w, hw⟩ := hw
  let O : M.ι × M'.ι → S.Opens := fun k =>
    (M.pull e).U (fun _ => k.1) ⊓ (M'.pull e).U (fun _ => k.2) ⊓ e ⁻¹ᵁ (M.U k.1 ⊓ M'.U k.2)
  let c : ∀ k, Γ(S, O k)ˣ := fun k =>
    res (inf_le_left.trans inf_le_left : O k ≤ _) (r.s fun _ => k.1) *
      (res (inf_le_left.trans inf_le_right : O k ≤ _) (r'.s fun _ => k.2))⁻¹ *
      (res (inf_le_right : O k ≤ _) (pullU e (M.U k.1 ⊓ M'.U k.2) (w.s k)))⁻¹

  have hc : ∀ a b x, x ∈ O (a, b) → gm (𝟙 S) x (O (a, b)) (c (a, b)) =
      gm (𝟙 S) x _ (r.s fun _ => a) * (gm (𝟙 S) x _ (r'.s fun _ => b))⁻¹ *
        (gm e x (M.U a ⊓ M'.U b) (w.s (a, b)))⁻¹ := by
    intro a b x hx
    simp only [c]
    rw [map_mul, map_mul, map_inv, map_inv, gm_res_eq_gm (𝟙 S) x _ hx, gm_res_eq_gm (𝟙 S) x _ hx,
      gm_res_eq_gm (𝟙 S) x _ hx]
    refine congrArg (HMul.hMul _) (congrArg Inv.inv ?_)
    exact gm_id_pull e x _ hx.2 _

  have hcomp : ∀ k l, res (inf_le_left : O k ⊓ O l ≤ O k) (c k) = res (inf_le_right : O k ⊓ O l ≤ O l) (c l) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩
    apply units_ext_of_gm_id_eq
    intro x hx
    have hk := hx.1
    have hl := hx.2
    rw [gm_res_eq_gm (𝟙 S) x _ hx, gm_res_eq_gm (𝟙 S) x _ hx, hc a b x hk, hc a' b' x hl,
      pull_gen hr x a a' hk.2.1 hl.2.1, pull_gen hr' x b b' hk.2.2 hl.2.2,
      gm_iso hw e x a a' b b' ⟨hk.2, hl.2⟩]
    exact comm_mul_mul_inv_mul_mul_inv_inv_eq _ _ _ _ _

  obtain ⟨s0, hs0, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf O (⨆ k, O k)
    (fun i => homOfLE (le_iSup O i)) le_rfl (fun i => (c i).val)
    (fun i j => congrArg Units.val (hcomp i j))
  obtain ⟨t0, ht0, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf O (⨆ k, O k)
    (fun i => homOfLE (le_iSup O i)) le_rfl (fun i => (c i).inv)
    (fun i j => congrArg Units.inv (hcomp i j))
  have hst : s0 * t0 = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' S.sheaf O (⨆ k, O k) (fun i => homOfLE (le_iSup O i)) le_rfl
    intro i
    rw [map_mul, map_one, hs0 i, ht0 i]
    exact (c i).val_inv
  have hts : t0 * s0 = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' S.sheaf O (⨆ k, O k) (fun i => homOfLE (le_iSup O i)) le_rfl
    intro i
    rw [map_mul, map_one, hs0 i, ht0 i]
    exact (c i).inv_val
  let c0 : Γ(S, ⨆ k, O k)ˣ := ⟨s0, t0, hst, hts⟩
  have hc0 : ∀ k, res (le_iSup O k) c0 = c k := fun k => Units.ext (hs0 k)

  have hpe : ∀ x, p (e x) = x := fun x => by
    have := congrArg (fun f => f.base x) he
    simpa using this
  have hk : ∀ k : M.ι × M'.ι, (LB.div M M').U k ≤ p ⁻¹ᵁ (⨆ k, O k) := by
    rintro ⟨a, b⟩ y hy
    have h1 : y ∈ ⨆ a, M.U a := TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy.1⟩
    have h2 : y ∈ ⨆ b, M'.U b := TopologicalSpace.Opens.mem_iSup.2 ⟨b, hy.2⟩
    rw [hV] at h1
    rw [hV'] at h2
    have h3 : e (p y) ∈ p ⁻¹ᵁ V := by
      show p (e (p y)) ∈ V
      rw [hpe]
      exact h1
    have h4 : e (p y) ∈ p ⁻¹ᵁ V' := by
      show p (e (p y)) ∈ V'
      rw [hpe]
      exact h2
    rw [← hV] at h3
    rw [← hV'] at h4
    obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 h3
    obtain ⟨b', hb'⟩ := TopologicalSpace.Opens.mem_iSup.1 h4
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨(a', b'), ⟨⟨mem_pull_U_of_mem M e _ a' ha', mem_pull_U_of_mem M' e _ b' hb'⟩, ⟨ha', hb'⟩⟩⟩
  refine ⟨⟨fun k => w.s k * res (hk k) (pullU p _ c0)⟩, ?_, ?_⟩
  · intro i j
    dsimp only
    rw [map_mul, map_mul, hw i j, res_res_units', res_res_units', _root_.mul_assoc]
  · intro x a b hxa hxb
    have hx : x ∈ O (a, b) := ⟨⟨mem_pull_U_of_mem M e x a hxa, mem_pull_U_of_mem M' e x b hxb⟩, ⟨hxa, hxb⟩⟩
    have hxab : e x ∈ M.U a ⊓ M'.U b := ⟨hxa, hxb⟩
    have hx0 : x ∈ ⨆ k, O k := le_iSup O (a, b) hx
    have hz : x ∈ e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k)) := by
      show p (e x) ∈ ⨆ k, O k
      rw [hpe]
      exact hx0
    have hP : gm e x (M.U a ⊓ M'.U b) (res (hk (a, b)) (pullU p _ c0)) = gm (𝟙 S) x (O (a, b)) (c (a, b)) := by
      calc gm e x (M.U a ⊓ M'.U b) (res (hk (a, b)) (pullU p _ c0))
          = gm e x (p ⁻¹ᵁ (⨆ k, O k)) (pullU p _ c0) := gm_res_eq_gm e x (hk (a, b)) hxab _
        _ = gm (𝟙 S) x (e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k))) (pullU e _ (pullU p _ c0)) := (gm_id_pull e x _ hz _).symm
        _ = gm (𝟙 S) x (e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k))) (res le_rfl (pullU e _ (pullU p _ c0))) :=
          (gm_res_eq_gm (𝟙 S) x le_rfl hz _).symm
        _ = gm (e ≫ p) x (⨆ k, O k) c0 := gm_rp₂ e p x _ _ le_rfl hz c0
        _ = gm (𝟙 S) x (⨆ k, O k) c0 := by rw [he]
        _ = gm (𝟙 S) x (O (a, b)) (res (le_iSup O (a, b)) c0) := (gm_res_eq_gm (𝟙 S) x _ hx c0).symm
        _ = gm (𝟙 S) x (O (a, b)) (c (a, b)) := congrArg _ (hc0 (a, b))
    have hw' : gm e x (M.U a ⊓ M'.U b) (w.s (a, b) * res (hk (a, b)) (pullU p _ c0)) =
        gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x (O (a, b)) (c (a, b)) :=
      (map_mul _ _ _).trans (congrArg _ hP)
    refine Eq.trans ?_ (congrArg (· * gm (𝟙 S) x _ (r'.s fun _ => b)) hw'.symm)
    rw [hc a b x hx]
    exact eq_mul_mul_inv_mul_inv_mul _ _ _

end GlobalTheory.BundleNormalise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.lineBundle_trivial_iso_descend_field : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  first | exact @GlobalTheory.lb_gen_iso_descend_field | exact GlobalTheory.lb_gen_iso_descend_field | (intros; apply GlobalTheory.lb_gen_iso_descend_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_descent_of_morphisms_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  first | exact @GlobalTheory.morphisms_descend_to_large_subfield | exact GlobalTheory.morphisms_descend_to_large_subfield | (intros; apply GlobalTheory.morphisms_descend_to_large_subfield <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelObjectClass_prim_and_iso_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b (spMap em)), PELClass D a bas ρ em t → (a w = H.w0 → a w' = H.bar H.w0 → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → PELClass D a bas ρ em t' := by
  first | exact @GlobalTheory.pelClass_prim_and_iso | exact GlobalTheory.pelClass_prim_and_iso | (intros; apply GlobalTheory.pelClass_prim_and_iso <;> assumption)
end

