import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0132
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

section Linear

variable {ι O : Type} [Fintype ι] [CommRing O]
variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]

theorem mem_eig (ρ : O →+* Module.End R N) (σ : O →+* R) (u : N) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def Splits (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : Prop :=
  ∀ m : N, ∃! f : ι → N, (∀ s a, ρ a (f s) = τ s a • f s) ∧ ∑ s, f s = m

def sumMap (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : (∀ s, eigSp ρ (τ s)) →ₗ[R] N :=
  ∑ s, (eigSp ρ (τ s)).subtype ∘ₗ LinearMap.proj s

theorem sumMap_apply (ρ : O →+* Module.End R N) (τ : ι → O →+* R) (g : ∀ s, eigSp ρ (τ s)) :
    sumMap ρ τ g = ∑ s, (g s : N) := by
  simp [sumMap, LinearMap.sum_apply]

theorem sumMap_bij {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    Function.Bijective (sumMap ρ τ) := by
  constructor
  · intro g g' e
    have := (h (sumMap ρ τ g)).unique (y₁ := fun s => (g s : N)) (y₂ := fun s => (g' s : N))
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g s).2 a, (sumMap_apply ρ τ g).symm⟩
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g' s).2 a, by rw [e, sumMap_apply]⟩
    exact funext fun s => Subtype.ext (congrFun this s)
  · intro m
    obtain ⟨f, ⟨hf, hs⟩, -⟩ := h m
    exact ⟨fun s => ⟨f s, (mem_eig ρ (τ s) _).2 (hf s)⟩, by rw [sumMap_apply]; exact hs⟩

theorem exists_bases [DecidableEq ι] [IsLocalRing R] [Module.Finite R N] [Module.Projective R N]
    {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    ∃ r : ι → ℕ, Nonempty (∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) := by
  let e := LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h)
  haveI hP : Module.Projective R (∀ s, eigSp ρ (τ s)) := Module.Projective.of_equiv e.symm
  have key : ∀ s, Module.Free R (eigSp ρ (τ s)) ∧ Module.Finite R (eigSp ρ (τ s)) := fun s => by
    haveI : Module.Finite R (∀ s, eigSp ρ (τ s)) := Module.Finite.equiv e.symm
    haveI : Module.Finite R (eigSp ρ (τ s)) :=
      Module.Finite.of_surjective (LinearMap.proj s : (∀ s, eigSp ρ (τ s)) →ₗ[R] eigSp ρ (τ s))
        (fun y => ⟨Pi.single s y, by simp⟩)
    haveI : Module.Projective R (eigSp ρ (τ s)) :=
      Module.Projective.of_split (LinearMap.single R (fun s => eigSp ρ (τ s)) s) (LinearMap.proj s)
        (LinearMap.ext fun y => by simp)
    haveI : Module.FinitePresentation R (eigSp ρ (τ s)) := Module.finitePresentation_of_projective _ _
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  refine ⟨fun s => Module.finrank R (eigSp ρ (τ s)), ⟨fun s => ?_⟩⟩
  haveI := (key s).1
  haveI := (key s).2
  exact Module.finBasis R _

def totBasis [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) : Module.Basis (Σ s, Fin (r s)) R N :=
  (Pi.basis b).map (LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h))

theorem totBasis_apply [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (s : ι) (i : Fin (r s)) :
    totBasis h b ⟨s, i⟩ = b s i := by
  simp only [totBasis, Module.Basis.map_apply, LinearEquiv.ofBijective_apply, sumMap_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

variable {T N' : Type} [CommRing T] [AddCommGroup N'] [Module T N']

theorem image_frame [DecidableEq ι] {θ : R →+* T} {ρ : O →+* Module.End R N} {τ : ι → O →+* R}
    {ρ' : O →+* Module.End T N'} (h' : Splits ρ' fun s => θ.comp (τ s)) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (β : N →ₛₗ[θ] N')
    (B : Module.Basis (Σ s, Fin (r s)) T N') (hB : ∀ s i, B ⟨s, i⟩ = β (b s i))
    (hρ : ∀ a e, ρ' a (β e) = β (ρ a e)) (s : ι) :
    LinearIndependent T (fun i => β (b s i)) ∧
      Submodule.span T (Set.range fun i => β (b s i)) = eigSp ρ' (θ.comp (τ s)) := by
  have hv : ∀ s i, ∀ a, ρ' a (β (b s i)) = (θ.comp (τ s)) a • β (b s i) := fun s i a => by
    rw [hρ, (mem_eig ρ (τ s) _).1 (b s i).2 a, β.map_smulₛₗ]
    rfl
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_⟩
  · have := B.linearIndependent.comp (Sigma.mk s) sigma_mk_injective
    convert this using 1
    exact funext fun i => (hB s i).symm
  · rintro _ ⟨i, rfl⟩
    exact (mem_eig ρ' _ _).2 (hv s i)
  · let f : ι → N' := fun s' => ∑ i, B.repr w ⟨s', i⟩ • β (b s' i)
    have hf : ∀ s' a, ρ' a (f s') = (θ.comp (τ s')) a • f s' := fun s' a => by
      simp only [f, map_sum, Finset.smul_sum, map_smul, hv s']
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hsum : ∑ s', f s' = w := by
      have := B.sum_repr w
      rw [Fintype.sum_sigma] at this
      simpa only [f, hB] using this
    have hw' := (mem_eig ρ' _ _).1 hw
    have hu := (h' w).unique (y₁ := f) (y₂ := fun s' => if s' = s then w else 0) ⟨hf, hsum⟩
      ⟨fun s' a => by
        by_cases e : s' = s
        · subst e; simpa using hw' a
        · simp [e], by simp⟩
    have : w = f s := by simpa using (congrFun hu s).symm
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Linear

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

open GlobalTheory.CompanionTheory.Ar.LieVB

theorem splits_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {S : Type} [CommRing S] (κ : c.F →+* S) {N : Type} [AddCommGroup N] [Module S N]
    (ρ : 𝓞 E →+* Module.End S N) : Splits ρ (fun s : E →+* ℂ => κ.comp (tauIn c s)) := by
  letI : Algebra c.F S := κ.toAlgebra
  exact fun m => GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ m

theorem exists_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  classical
  intro E _ _ _ H l c X t A _ _ x κ σ
  haveI hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨N, _, _, ⟨M⟩⟩ := lieModel_exists X t.G A x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X t.G A x N M (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change X t.G A x N M
  have hsp := splits_of c κ ρ
  obtain ⟨r, ⟨b⟩⟩ := exists_bases hsp
  refine ⟨r σ, fun i => M.pt (b σ i), ?_⟩
  intro T _ θ x' hx' v hv
  subst hx'
  obtain ⟨N', _, _, ⟨M'⟩⟩ := lieModel_exists X t.G T (spMap θ ≫ x)
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act X t.G T (spMap θ ≫ x) N' M' (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  let q := Fintype.equivFin (Σ s, Fin (r s))
  obtain ⟨β, B, hB, hβ⟩ := basis_tr θ x (spMap θ ≫ x) rfl M M' ((totBasis hsp b).reindex q)
  have hB' : ∀ s i, (B.reindex q.symm) ⟨s, i⟩ = β (b s i) := fun s i => by
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      totBasis_apply]
  have hact : ∀ a e, ρ' a (β e) = β (ρ a e) := fun a e => pt_left_inj M' (by
    rw [hβ, hρ a e, Over.comp_left, ← Category.assoc, ← hβ e, hρ' a (β e), Over.comp_left])
  have hsp' : Splits ρ' (fun s : E →+* ℂ => θ.comp (κ.comp (tauIn c s))) := splits_of c (θ.comp κ) ρ'
  obtain ⟨hli, hspan⟩ := image_frame hsp' b β (B.reindex q.symm) hB' hact σ
  have hvv : v = fun k => M'.pt (β (b σ k)) := funext fun k => Over.OverMorphism.ext (by
    rw [hv k, hβ])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action X T t.G (spMap θ ≫ x) N' M').2 (𝓞 E) t.act ρ' ((θ.comp κ).comp (tauIn c σ)) hρ').2 _ _).2
    ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionExteriorValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem tied_pull (Y : Model Xo c β) {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F)
    {y : Sp B ⟶ Xo.XF c} {y' : Sp F ⟶ Xo.XF c} (hy : y' = spMap ψ ≫ y)
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    Tied Y y' (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V') := by
  subst hy
  obtain ⟨u, h1, h2, h3⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ u, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_alg ψ
  · rw [Category.assoc, h2]
  · rw [Category.assoc, h3]

theorem tied_over (Y : Model Xo c β) {B : Type} [CommRing B] {y : Sp B ⟶ Xo.XF c}
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    V ≫ Xo.univ.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ under y := by
  obtain ⟨u, h1, rfl, -⟩ := h
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  rw [Category.assoc, hp.w, ← Category.assoc, h1, Category.assoc]

theorem isCombAt_pull {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F) {x : Sp B ⟶ Xo.X} {x' : Sp F ⟶ Xo.X}
    (hx : spMap ψ ≫ x = x') {m : ℕ} {vs : Fin m → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)} {cf : Fin m → B}
    {w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vs cf w) :
    Formalism.L2.Pj.IsCombAt x' (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (fun k => ψ (cf k))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let P : Formalism.L2.Pj.tEps x' ⟶ Formalism.L2.Pj.tEps x := epsBase ψ hx
  let Q : (Formalism.L2.Pj.tEps x ⟶ Xo.univ.t.G) →* (Formalism.L2.Pj.tEps x' ⟶ Xo.univ.t.G) :=
    { toFun := fun f => P ≫ f, map_one' := comp_one _, map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => P ≫ u i, fun i => ?_, ?_⟩
  · change spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_eps ψ (cf i)
  · have : (List.ofFn fun i => P ≫ u i).prod = P ≫ (List.ofFn u).prod := by
      change (List.ofFn fun i => Q (u i)).prod = Q (List.ofFn u).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [this]
    rfl

theorem exists_pulled (Y : Model Xo c β) {B F : Type} [CommRing B] [Field F] (ψ : B →+* F) (yB : Sp B ⟶ Xo.XF c)
    (y : Sp F ⟶ Xo.XF c) (hy : y = spMap ψ ≫ yB) (x₀ : Sp B ⟶ Xo.X) (hx₀ : x₀ = under yB) {n : ℕ} (v : Vecs y n)
    (vs : Fin n → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left))
    (hv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (C : Matrix (Fin n) (Fin n) B)
    (ee : Fin n → (Sp (DualNumber B) ⟶ Y.t.G.left))
    (hV : ∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y yB V (ee i) ∧
      Formalism.L2.Pj.IsCombAt x₀ vs (C i) V) :
    ∃ v₀ : Vecs y n, (∀ i, IsComb ((ψ.mapMatrix C) i) v (v₀ i)) ∧
      ∀ i, Tied Y y (v₀ i).left (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ ee i) := by
  choose V hT hC using hV
  have hT' := fun i => tied_pull Y ψ hy (hT i)
  refine ⟨fun i => Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V i) (tied_over Y (hT' i)), fun i => ?_, hT'⟩
  rw [GlobalTheory.CompanionTheory.Ar.FrameEig.isComb_iff]
  have hx : spMap ψ ≫ x₀ = under y := by
    rw [hx₀, hy]
    exact (Category.assoc _ _ _).symm
  have := isCombAt_pull ψ hx (hC i)
  simp only [← hv] at this
  exact this

theorem exists_germ (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (hφ : spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hU : Set.range y ⊆ U) (θF : R →+* F) (hθ : spMap θF ≫ x = y ≫ Y.j) :
    ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))),
      spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)) ∧
      (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂ ∧
      (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF := by
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := by
    have h1 : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint F) := (Z.closure _).1 (hU ⟨_, rfl⟩)
    have h2 := h1.map Y.j.continuous
    simp only [genPt, centre, Scheme.Hom.comp_apply]
    exact h2
  have hqr : centre (y ≫ Y.j) ∈ x.opensRange := by
    rw [← hθ]
    change (spMap θF ≫ x) (IsLocalRing.closedPoint F) ∈ Set.range x
    simp only [Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hqx : (Y.X.fromSpecStalk (centre (y ≫ Y.j)))
      (IsLocalRing.closedPoint (Y.X.presheaf.stalk (centre (y ≫ Y.j)))) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨θ', hθ'⟩ := exists_lift (A := Y.X.presheaf.stalk (centre (y ≫ Y.j))) x _ hqx
  refine ⟨h, θ', hθ', ?_, ?_⟩
  · have h1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') ≫ x = spMap φ₂ ≫ x := by
      have e1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') =
          spMap (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩) ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hφ]
      exact spec_genMap _ _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))
  · have h1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') ≫ x = spMap θF ≫ x := by
      have e1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') =
          spMap (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hθ]
      exact spec_centre _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem valAt_of_chart (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) (φ₂ : R →+* Z.Ω) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (θF : R →+* F)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j)))
    (h₁ : spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)))
    (h₂ : (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂)
    (h₃ : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF) (b : Z.V) (e : epsAt x ⟶ Y.t.G)
    (ht : GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x e) (hb : (Z.M.pt b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ e.left)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) (hv' : v'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θF) ≫ e.left) :
    Z.M.ValAt (y ≫ Y.j) b v' := by
  refine ⟨h, epsBase θ' h₁ ≫ e, ⟨isTanAt_base _ _ ht, ?_⟩, ?_⟩
  · rw [hb, ← h₂, ← spMap_dual_comp]
    simp [epsBase, spMap]
  · rw [hv', ← h₃, ← spMap_dual_comp]
    simp [epsBase, spMap]

theorem sameVec_of_tied (Y : Model Xo c β) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G} {w : Sp (DualNumber F) ⟶ Y.t.G.left}
    (h : Tied Y y v.left w) (hw : w = v'.left) : SameVec Y y v v' := by
  subst hw
  exact h

end GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

theorem GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (B : Type) [CommRing B] [Algebra S B] (θ : R →+* B) (C₁ : Matrix (Fin D.p) (Fin D.p) B) (C₂ : Matrix (Fin D.q) (Fin D.q) B), IsLineFn U τ φ → Represents Y U τ Z.M a b φ → spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j → a = α • exteriorPower.ιMulti Z.Ω D.p b₁ → b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → φ₂ f = α / κ → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) → (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) → spMap θ ≫ x = spMap (algebraMap S B) ≫ zPt z ≫ Y.j → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) → ∀ (F : Type) [Field F] (ψ : B →+* F) (y : Sp F ⟶ Xo.XF c), y = spMap ψ ≫ spMap (algebraMap S B) ≫ zPt z → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → φ F y v w * ψ C₂.det = ψ (θ f) * ψ C₁.det := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ a b S _ _ z hp hq R _ x _ φ₂ e₁ e₂ f b₁ b₂ α κ B _ _ θ C₁ C₂ hφ hrep hξ ha hb
    hf ht₁ ht₂ hb₁ hb₂ hθ hC₁ hC₂ hV₁ hV₂ F _ ψ y hy hU v w hv hw
  have e0 : ∀ {A : Type} [CommRing A] (g : A →+* B), spMap (ψ.comp g) = spMap ψ ≫ spMap g := fun g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hyS : under y = spMap (ψ.comp (algebraMap S B)) ≫ z.x := by
    rw [hy, e0]
    simp only [under, Category.assoc, zPt_fst]
  have hys : y ≫ pullback.snd _ _ = spMap ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) := by
    rw [hy]
    simp only [Category.assoc, zPt_snd]
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨v', w', hv', hw', hfr⟩ := GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt E H D l Xo c τ S z F (ψ.comp (algebraMap S B)) y
    hp hq hyS hys
  have ev : v' = v := funext fun i => Over.OverMorphism.ext ((hv' i).trans (hv i).symm)
  have ew : w' = w := funext fun i => Over.OverMorphism.ext ((hw' i).trans (hw i).symm)
  rw [ev, ew] at hfr
  have hF := hfr U hU
  have hzx : spMap (algebraMap S B) ≫ z.x = under (spMap (algebraMap S B) ≫ zPt z) := by
    simp only [under, Category.assoc, zPt_fst]
  have hvv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) := fun k => by
    rw [hv k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  have hww : ∀ k, (w k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) := fun k => by
    rw [hw k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  obtain ⟨v₀, hc₁, hT₁⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx v _ hvv C₁
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) hV₁
  obtain ⟨w₀, hc₂, hT₂⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx w _ hww C₂
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) hV₂
  have hu₁ : IsUnit (ψ.mapMatrix C₁).det := by
    rw [← RingHom.map_det]; exact hC₁.map ψ
  have hu₂ : IsUnit (ψ.mapMatrix C₂).det := by
    rw [← RingHom.map_det]; exact hC₂.map ψ
  have hF₀ : IsFramed U τ ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) y v₀ w₀ :=
    ⟨hF.1, hF.2.1, GlobalTheory.T.eigen_frame_of_unit_det_change Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.p v v₀ (ψ.mapMatrix C₁) hF.2.2.1 hc₁ hu₁,
      GlobalTheory.T.eigen_frame_of_unit_det_change Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.q w w₀ (ψ.mapMatrix C₂) hF.2.2.2 hc₂ hu₂⟩
  have hθF : spMap (ψ.comp θ) ≫ x = y ≫ Y.j := by
    rw [e0, Category.assoc, hθ, hy]
    simp only [Category.assoc]
  obtain ⟨h, θ', g₁, g₂, g₃⟩ := FieldStage.exists_germ Y Z x φ₂ hξ y hU (ψ.comp θ) hθF
  have hval₁ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₁ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₁ i) (e₁ i) (ht₁ i) (hb₁ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₁ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  have hval₂ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₂ i) v' ∧ SameVec Y y (w₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₂ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₂ i) (e₂ i) (ht₂ i) (hb₂ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₂ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  obtain ⟨h', s, hs₁, hs₂⟩ := hrep F _ y v₀ w₀ b₁ b₂ α κ hF₀ ha hb hval₁ hval₂
  have hs : s = θ' f := Z.gen.inj ⟨_, h'⟩ (hs₁.trans (hf.symm.trans (by rw [← g₂]; rfl)))
  have hvalue : φ F y v₀ w₀ = ψ (θ f) := by
    rw [← hs₂, hs]
    exact RingHom.congr_fun g₃ f
  have hchg := hφ.chg F _ y v w v₀ w₀ (ψ.mapMatrix C₁) (ψ.mapMatrix C₂) hF hF₀ hc₁ hc₂
  rw [hvalue, ← RingHom.map_det, ← RingHom.map_det] at hchg
  exact hchg.symm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenCondition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

theorem exists_open_forall {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (p : Cpt ξ) {I : Type} [Finite I]
    (P : I → Cpt ξ → Prop) (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  classical
  have := Fintype.ofFinite I
  have key : ∀ s : Finset I, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i ∈ s, P i q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, trivial, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨U, hU, HU⟩ := ih
      obtain ⟨V, hV, HV⟩ := h a
      refine ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact HV q hq.2
      · exact HU q hq.1 i hi
  obtain ⟨U, hU, HU⟩ := key Finset.univ
  exact ⟨U, hU, fun q hq i => HU q hq i (Finset.mem_univ i)⟩

theorem exists_open_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  obtain ⟨U, hU, HU⟩ := exists_open_forall p (fun (j : Fin n) (q : Cpt ξ) => (f j : Ω) ∈ regAt ξ q)
    fun j => exists_open_mem_regAt ξ p _ (f j).2
  refine ⟨U, hU, fun q hq => ?_⟩
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (⟨(f j : Ω), HU q hq j⟩ : regAt ξ q) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem mem_span_field_of_mem_span_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type}
    [AddCommGroup E] [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) : e ∈ Submodule.span Ω (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (f j : Ω) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_span_and_nhd : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  intro X G _ _ _ Ω _ ξ E _ _ M p g b hb
  obtain ⟨R, _, x, hx, F, _, _, MR, n, bR, hp⟩ := exists_chart G p.1
  have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR bR ξ M φ hφ
  have hc : ∀ q : Cpt ξ, q.1 ∈ x.opensRange → M.lat.IsFrameAt c q := by
    intro q hq
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  have hbc : Submodule.span (regAt ξ p) (Set.range b) = Submodule.span (regAt ξ p) (Set.range c) :=
    hb.2.symm.trans (hc p hp).2
  have hbi : ∀ i, b i ∈ Submodule.span (regAt ξ p) (Set.range c) := fun i => by
    rw [← hbc]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcj : ∀ j, c j ∈ Submodule.span (regAt ξ p) (Set.range b) := fun j => by
    rw [hbc]
    exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨top_le_iff.1 (hsp.ge.trans (Submodule.span_le.2 ?_)), ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact mem_span_field_of_mem_span_regAt ξ p b _ (hcj j)
  obtain ⟨U, hU, HU⟩ := exists_open_forall p
    (fun (i : Fin g) (q : Cpt ξ) => b i ∈ Submodule.span (regAt ξ q) (Set.range c))
    fun i => exists_open_mem_span ξ p c _ (hbi i)
  obtain ⟨V, hV, HV⟩ := exists_open_forall p
    (fun (j : Fin n) (q : Cpt ξ) => c j ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun j => exists_open_mem_span ξ p b _ (hcj j)
  refine ⟨x.opensRange ⊓ (U ⊓ V), ⟨hp, hU, hV⟩, fun q hq => ⟨hb.1, ?_⟩⟩
  rw [(hc q hq.1).2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact HV q hq.2.2 j
  · rintro _ ⟨i, rfl⟩
    exact HU q hq.2.1 i

end GlobalTheory.CompanionTheory.Ar.LieVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_isBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (j e))) → IsBaseChange R' j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange | exact GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange <;> assumption)
end

