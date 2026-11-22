import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0026
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImage
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.CarriesAt

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

theorem par_of_tri {h : Mat m K} (hd : ∀ τ i, h τ i i ≠ 0) (hl : ∀ τ i k, i < k → h τ i k = 0) : Par m ⊤ h := fun τ => by
  have hdet : (h τ).det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular (h τ) fun i j hij => hl τ i j hij]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd τ i
  exact ⟨fun _ _ => trivial, hdet, trivial, fun i j _ hij => hl τ i j hij⟩

theorem Par.diag_ne {O : Subring K} {h : Mat m K} (hp : Par m O h) (τ : ι) (i : Fin (m τ)) : h τ i i ≠ 0 := by
  have := hp.det_ne τ
  rw [Matrix.det_of_lowerTriangular (h τ) fun a b hab => (hp τ).2.2.2 a b a.2 hab] at this
  exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_cast {R : Type} [CommRing R] {φ : c.F →+* R} {x x' : Sp R ⟶ Z.X} (h : x = x') (g : EigFrame Z φ x) :
    ∃ g' : EigFrame Z φ x', ∀ τ i, g'.v τ i = g.v τ i := by
  subst h
  exact ⟨g, fun _ _ => rfl⟩

theorem spMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (dualMap (ψ.comp ρ)) = spMap (dualMap ψ) ≫ spMap (dualMap ρ) := by
  have e : dualMap (ψ.comp ρ) = (dualMap ψ).comp (dualMap ρ) := by
    ext r <;> simp [dualMap]
  rw [e]
  simp [spMap, Spec.map_comp]

theorem coord_of_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {g : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''} {A : Mat Dw.mult R''}
    (hx : x' = spMap ρ ≫ x) (hφ : φ' = ρ.comp φ) (hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i)
    (h : f.Coord (ψ.comp ρ) g A) : f'.Coord ψ g A := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, hx, ← Category.assoc]
    congr 1
    simp [spMap, Spec.map_comp]
  · rw [h2, hφ, RingHom.comp_assoc]
  · have e : (fun k => spMap (dualMap ψ) ≫ f'.v τ k) = fun k => spMap (dualMap (ψ.comp ρ)) ≫ f.v τ k := by
      funext k
      rw [hv, spMap_dualMap_comp, Category.assoc]
    rw [e]
    exact h3 τ i

theorem algebraMap_eq_comp_specializes {X : Scheme.{0}} [IsIntegral X] {y y' : X} (h : y' ⤳ y) :
    algebraMap (X.presheaf.stalk y) X.functionField =
      (algebraMap (X.presheaf.stalk y') X.functionField).comp (X.presheaf.stalkSpecializes h).hom :=
  (congrArg CommRingCat.Hom.hom
    (TopCat.Presheaf.stalkSpecializes_comp X.presheaf (genericPoint_specializes y') h)).symm

theorem exists_adapted {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {S : Fr (ratOf C.Y) Dw.mult Dw.mult}
    {A₀ : Mat Dw.mult C.Y.Fn} (hA₀ : A₀ ∈ S.S (genericPoint C.Y.X))
    (hTied : ∀ y : C.Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* C.Y.X.presheaf.stalk y)
      (f : EigFrame Z φ (stalkPt C.Y y ≫ C.π ≫ genι Z)),
      f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (A₀ * A⁻¹))
    {K : Type} [Field K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z φ x) {y y' : C.Y.X} (hsp : y' ⤳ y)
    (ψ' : C.Y.X.presheaf.stalk y' →+* K) {φ₁ : c.F →+* C.Y.X.presheaf.stalk y}
    (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) {T : Mat Dw.mult C.Y.Fn} {h : Mat Dw.mult K}
    (hT1 : f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 T)
    (hT : Par Dw.mult ⊤ T)
    (hh1 : f.Coord (ψ'.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) g h) :
    ∃ A ∈ S.S y', ∃ (φ₂ : c.F →+* C.Y.X.presheaf.stalk y') (f₁ : EigFrame Z φ₂ (stalkPt C.Y y' ≫ C.π ≫ genι Z)),
      f₁.Coord (algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord ψ' g h := by
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set alg := algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField with halg
  have hρ : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y y' := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hinj : Function.Injective alg := IsFractionRing.injective _ _

  have hfS : f.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f inferInstance
  obtain ⟨f₀, hf₀⟩ := hfS (C.Y.X.presheaf.stalk y') ρ
  have hx' : spMap ρ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z = stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨f', hf'⟩ := exists_cast hx' f₀
  have hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i := fun τ i => (hf' τ i).trans (hf₀ τ i)
  have hT1' : f'.Coord alg C.f0 T :=
    coord_of_bc hx'.symm rfl hv (algebraMap_eq_comp_specializes hsp ▸ hT1)
  have hh1' : f'.Coord ψ' g h := coord_of_bc hx'.symm rfl hv hh1

  obtain ⟨A', hA'⟩ := S.nonempty y'
  obtain ⟨φ'', f'', hf''⟩ := hTied y' A' hA'
  obtain rfl : φ'' = ρ.comp φ₁ := RingHom.ext fun a => hinj (by
    have e1 := RingHom.congr_fun hf''.2.1 a
    have e2 := RingHom.congr_fun hT1'.2.1 a
    exact e1.symm.trans e2)
  have hS'' : f''.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f'' inferInstance
  have hid : stalkPt C.Y y' ≫ C.π ≫ genι Z = spMap (RingHom.id _) ≫ stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk y')) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨G, hG, -⟩, hGu⟩ := (GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ (ρ.comp φ₁) _ (RingHom.id _) inferInstance hS''
    hid (RingHom.id_comp _).symm).1 f'
  have hGd := hGu G hG
  have hcomp : f''.Coord alg C.f0 (T * G.map alg) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ f'' _ _ _ f' _ _ _ C.f0 (RingHom.id _) alg G T inferInstance hG hT1'
    rwa [RingHom.comp_id] at this
  have heq : A₀ * A'⁻¹ = T * G.map alg :=
    (((GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ _ _ alg inferInstance hS'' hf''.1 hf''.2.1).1 C.f0).1).unique hf'' hcomp
  have hAA : T⁻¹ * A₀ * A'⁻¹ = G.map alg := by
    rw [mul_assoc, heq, ← mul_assoc, Mat.inv_mul hT.det_ne, one_mul]
  have hPg : Par Dw.mult ((ratOf C.Y).O (genericPoint C.Y.X)).toSubring (A₀ * A'⁻¹) :=
    (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hA₀
  have hlow : Par Dw.mult ⊤ (G.map alg) := by
    rw [← hAA, mul_assoc]
    exact hT.inv.mul (hPg.mono le_rfl le_top)
  have hpar : Par Dw.mult ((ratOf C.Y).O y').toSubring (T⁻¹ * A₀ * A'⁻¹) := fun τ => by
    rw [hAA]
    have hdet : (G.map alg τ).det = alg (G τ).det := (alg.map_det (G τ)).symm
    obtain ⟨u, hu⟩ := hGd τ
    refine ⟨fun i j => mem_O_ratOf.2 ⟨G τ i j, rfl⟩, hlow.det_ne τ, ?_, fun i j hi hij => (hlow τ).2.2.2 i j hi hij⟩
    refine mem_O_ratOf.2 ⟨(u⁻¹ : (C.Y.X.presheaf.stalk y')ˣ), ?_⟩
    rw [hdet, ← hu]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨T⁻¹ * A₀, (Fr.mem_iff hA').2 hpar, ρ.comp φ₁, f', ?_, hh1'⟩
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hA₀
  rw [Mat.mul_inv_rev, Mat.inv_inv hT.det_ne, ← mul_assoc, Mat.mul_inv hA₀d, one_mul]
  exact hT1'

theorem carries_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (S : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult C.Y.Fn) (K : Type) [Field K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp K ⟶ C.Y.X), Tied e C.Y C.π C.f0 S A₀ → (C.Carries p g ↔ ∃ A ∈ S.S (p (IsLocalRing.closedPoint K)), ∃ (φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) (f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)) (h : Mat Dw.mult K), f₁.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g h ∧ Par Dw.mult ⊤ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C S A₀ K _ φ x g p hT
  obtain ⟨hA₀, hTied⟩ := hT
  constructor
  · rintro ⟨y, ψ, φ₁, f, t, t', hp, hf, hg⟩
    obtain ⟨T, hT1, hT2, hT3⟩ := (f.tri_iff _ C.f0 t).1 hf
    obtain ⟨h, hh1, hh2, hh3⟩ := (f.tri_iff _ g t').1 hg
    have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
      have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
        rw [hp]
        exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
      have e1 := spMap_stalkClosedPointTo p
      have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
      have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
          spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
        simp [spMap, Spec.map_comp]
      rw [e3, Category.assoc, e2, e1]
      exact hp.symm
    obtain ⟨A, hA, φ₂, f₁, c1, c2⟩ := exists_adapted C hA₀ hTied g hsp _ f hT1
      (par_of_tri (fun τ i => by rw [hT2]; exact Units.ne_zero _) hT3) (hψ ▸ hh1)
    exact ⟨A, hA, φ₂, f₁, h, c1, c2, par_of_tri (fun τ i => by rw [hh2]; exact Units.ne_zero _) hh3⟩
  · rintro ⟨A, hA, φ₁, f₁, h, h1, h2, h3⟩
    have hgen := Fr.mem_genericPoint hA
    have hP : Par Dw.mult ⊤ (A₀ * A⁻¹) := ((Fr.mem_iff hgen).1 hA₀).mono le_rfl le_top
    refine ⟨_, (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom, φ₁, f₁,
      fun τ i => Units.mk0 _ (Par.diag_ne hP τ i), fun τ i => Units.mk0 _ (Par.diag_ne h3 τ i),
      (spMap_stalkClosedPointTo p).symm, (f₁.tri_iff _ C.f0 _).2 ⟨_, h1, fun _ _ => rfl, fun τ i k hik => (hP τ).2.2.2 i k i.2 hik⟩,
      (f₁.tri_iff _ g _).2 ⟨h, h2, fun _ _ => rfl, fun τ i k hik => (h3 τ).2.2.2 i k i.2 hik⟩⟩

end GlobalTheory.ShFam.CarriesAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernConnectionCurvaturePolyRepEval
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix

namespace GlobalTheory.GoodMetric

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem contDiffAt_aeval_int {σ : Type} {k : WithTop ℕ∞} {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ k (fun x => f x s) z) (P : MvPolynomial σ ℤ) :
    ContDiffAt ℝ k (fun x => aeval (f x) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, aeval_X]; exact hp.mul (hf s)

theorem del_aeval_int {σ : Type} [Fintype σ] {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ 1 (fun x => f x s) z) (P : MvPolynomial σ ℤ) (ξ : E) :
    del (fun x => aeval (f x) P) z ξ = ∑ s, aeval (f z) (pderiv s P) * del (fun x => f x s) z ξ := by
  classical
  have hd : ∀ Q : MvPolynomial σ ℤ, DifferentiableAt ℝ (fun x => aeval (f x) Q) z :=
    fun Q => (contDiffAt_aeval_int hf Q).differentiableAt one_ne_zero
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, pderiv_C, del_const]; simp
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    rw [del_add (hd p) (hd q)]; rfl
  | mul_X p s hp =>
    simp only [map_mul, aeval_X]
    rw [del_mul (hd p) ((hf s).differentiableAt one_ne_zero), hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, Pi.single_apply]
    congr 1
    · rw [Finset.sum_eq_single s] <;> simp +contextual [eq_comm]
    · exact Finset.sum_congr rfl fun _ _ => by ring

variable {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m)

theorem PolyRep.conn_ev {G : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => G w τ) u)
    (hu : ∀ τ, (G u τ).det ≠ 0) (ξ : E) :
    conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  set B : Mat m ℂ := (fun τ => (G u τ)ᵀ)⁻¹ with hB
  have hBu : B * (fun τ => (G u τ)ᵀ) = 1 := Mat.inv_mul fun τ => by rw [Matrix.det_transpose]; exact hu τ
  have hev : ∀ w, ρ.ev (B * fun τ => (G w τ)ᵀ) = ρ.ev B * (ρ.ev (G w))ᵀ := fun w => by
    rw [PolyRep.ev, ρ.mul, ρ.transp]; rfl
  have hinv : (ρ.ev (G u))ᵀ⁻¹ = ρ.ev B :=
    Matrix.inv_eq_left_inv (by rw [← hev, hBu]; exact ρ.one ℂ)
  have hρ : MContDiffAt 1 (fun w => ρ.ev (G w)) u := fun i j =>
    contDiffAt_aeval_int (f := fun w (v : EntIx m) => G w v.1 v.2.1 v.2.2) (fun v => h v.1 v.2.1 v.2.2) _
  have hK : ∀ τ, MContDiffAt 1 (fun w => B τ * (G w τ)ᵀ) u := fun τ =>
    (mContDiffAt_const _).mul (h τ).transpose
  have e1 : conn (fun w => ρ.ev (G w)) u ξ = mdel (fun w => ρ.ev (B * fun τ => (G w τ)ᵀ)) u ξ := by
    simp only [hev]
    rw [mdel_mul (mContDiffAt_const _) hρ.transpose, mdel_const, Matrix.zero_mul, add_zero, conn, hinv]
    rfl
  have e2 : ∀ τ, conn (fun w => G w τ) u ξ = mdel (fun w => B τ * (G w τ)ᵀ) u ξ := fun τ => by
    rw [mdel_mul (mContDiffAt_const _) (h τ).transpose, mdel_const, Matrix.zero_mul, add_zero, conn]
    rfl
  rw [e1]
  simp only [e2]
  ext i j
  refine (del_aeval_int (f := fun w (v : EntIx m) => (B * fun τ => (G w τ)ᵀ : Mat m ℂ) v.1 v.2.1 v.2.2)
    (fun v => hK v.1 v.2.1 v.2.2) (ρ.ent i j) ξ).trans ?_
  rw [hBu]
  rfl

theorem PolyRep.mdbar_lie {A : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => A w τ) u) (η : E) :
    mdbar (fun w => ρ.lie (A w)) u η = ρ.lie (fun τ => mdbar (fun w => A w τ) u η) := by
  ext i j
  simp only [mdbar_apply, PolyRep.lie, Matrix.of_apply]
  rw [dbar_sum fun v _ => (differentiableAt_const _).fun_mul ((h v.1).diff v.2.1 v.2.2),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h v.1).diff v.2.1 v.2.2)]
  simp

theorem PolyRep.eventually_conn_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) :
    ∀ᶠ u in 𝓝 v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  filter_upwards [eventually_all.2 fun τ => (h τ).eventually_two,
    eventually_all.2 fun τ => (h τ).eventually_isUnit (hv τ).isUnit] with u h1 h2 ξ
  exact ρ.conn_ev (fun τ => (h1 τ).of_le one_le_two) (fun τ => (h2 τ).ne_zero) ξ

theorem PolyRep.curv_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) (ξ η : E) :
    curv (fun w => ρ.ev (G w)) v ξ η = ρ.lie (fun τ => curv (fun w => G w τ) v ξ η) := by
  rw [curv, mdbar_congr ((ρ.eventually_conn_ev h hv).mono fun u hu => hu ξ),
    ρ.mdbar_lie (A := fun u τ => conn (fun w => G w τ) u ξ)
      (fun τ => (h τ).conn (hv τ).isUnit (by norm_num) ξ)]
  ext i j
  simp [PolyRep.lie, curv]

end General

theorem PolyRep.lie_sum_C_mul_X {ι κ : Type} [Fintype ι] [Fintype κ] {m : ι → ℕ} (ρ : PolyRep m)
    (F : κ → κ → Mat m ℂ) :
    (Matrix.of fun i j => ∑ a, ∑ b, C (ρ.lie (F a b) i j) * X (a, b) : Matrix _ _ (MvPolynomial (κ × κ) ℂ)) =
      ρ.lie fun τ => Matrix.of fun i j => ∑ a, ∑ b, C (F a b τ i j) * X (a, b) := by
  have hc : ∀ (S : Type) [CommRing S] (φ : ℂ →+* S) (P : MvPolynomial (EntIx m) ℤ),
      aeval (fun w : EntIx m => (1 : Mat m S) w.1 w.2.1 w.2.2) P =
        φ (aeval (fun w : EntIx m => (1 : Mat m ℂ) w.1 w.2.1 w.2.2) P) := fun S _ φ P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [aeval_C, aeval_C, eq_intCast, eq_intCast, map_intCast]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, Pi.one_apply, Pi.one_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
  refine Matrix.ext fun i j => ?_
  have key : ∀ (c : EntIx m → ℂ) (f : κ → κ → EntIx m → ℂ),
      (∑ a, ∑ b, C (∑ v, c v * f a b v) * X (a, b) : MvPolynomial (κ × κ) ℂ) =
        ∑ v, C (c v) * ∑ a, ∑ b, C (f a b v) * X (a, b) := fun c f => by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [eq_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  simp only [PolyRep.lie, Matrix.of_apply]
  rw [key]
  exact Finset.sum_congr rfl fun v _ => by rw [hc _ C]

theorem conn_curvPoly_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n),
    (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) →
    (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧
      curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  intro ι _ m ρ n G v h hv
  refine ⟨ρ.eventually_conn_ev h hv, ?_⟩
  simp only [curvPoly, ρ.curv_ev h hv]
  exact ρ.lie_sum_C_mul_X fun a b τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)

end GlobalTheory.GoodMetric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
section
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.PeriodFrame

open GlobalTheory.ShFam.Hor

def combMat {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k i => ∑ m, (ε i m : ℂ) * l m k

def perTau {n g r₀ r : ℕ} (a : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ)
    (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ) (s : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (D : ℂ) • ((combMat (ζ (logExp a s)) α)⁻¹ * combMat (lam s) φ)

theorem combMat_comb {g r r' : ℕ} (w : Fin r' → Fin g → ℂ) (l : Fin r → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ)
    (α : Matrix (Fin g) (Fin r') ℚ) (hw : ∀ i, w i = ∑ j, c i j • l j) :
    combMat w α = combMat l (α * c.map (Int.cast : ℤ → ℚ)) := by
  ext k i
  simp only [combMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hw, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by
    simp only [Pi.mul_apply, Pi.intCast_apply]; ring

theorem combMat_add_mul {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (φ + bᵀ * ε) = combMat l φ + combMat l ε * b.map (Rat.cast : ℚ → ℂ) := by
  ext k j
  simp only [combMat, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem combMat_shift {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) (D : ℕ) (Bk : Matrix (Fin g) (Fin g) ℤ) (hP : IsUnit (combMat l ε).det)
    (hB : ∀ i j, (Bk i j : ℚ) = D * b i j) :
    (D : ℂ) • ((combMat l ε)⁻¹ * combMat l (φ + bᵀ * ε)) =
      (D : ℂ) • ((combMat l ε)⁻¹ * combMat l φ) + Bk.map (Int.cast : ℤ → ℂ) := by
  rw [combMat_add_mul, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, smul_add]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have h := congrArg (Rat.cast : ℚ → ℂ) (hB i j)
  push_cast at h
  rw [h]

theorem shift_mem {n a : ℕ} (ha : a ≤ n) (k : Fin a) {s : Fin n → ℂ} (hs : s ∈ logDom n a) :
    s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I) ∈ logDom n a ∧
      logExp a (s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) = logExp a s := by
  simp only [logDom, Set.mem_setOf_eq] at hs ⊢
  constructor
  · intro j
    have h := hs j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [hk, if_true] at h ⊢
      simpa [Pi.add_apply] using h
    · simpa [Pi.add_apply, Pi.single_eq_of_ne hj] using h
  · funext j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, _root_.mul_one]
    · simp [logExp, Pi.single_eq_of_ne hj]

end GlobalTheory.PeriodFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {M : ModelsOf F r}

theorem exists_isThetaPt_of_adapted {k : Fin F.n} (T : ThetaData e F M k) (x : Fin T.m → ℂ)
    (hx : x ∈ T.co ⁻¹' (M.X k).dom) (y : FrPt Xo c (CAt σ)) (h₁ : y.x = F.u k (T.Pf (T.co x)))
    (h₂ : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co x)) z).left)
      (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) :
    ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt T x a y := by
  obtain ⟨hu, hsym, hpos, -⟩ := T.norm x hx
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨t, ht⟩ := T.fr_sec x hx
  obtain ⟨a, ha, hv⟩ := GlobalTheory.GenFactor.exists_factor GlobalTheory.abelianSchemeLaws_all.2.secTwist y.x _ h₁ y.s y.gen
    (F.ex k (T.Pf (T.co x))) (fun z => thetaChar (T.ta x) T.c₁ T.c₂ (T.h x *ᵥ z)) (fun j z => T.fr j (x, z))
    ⟨(T.h x)⁻¹ *ᵥ w, by
      show thetaChar _ _ _ (T.h x *ᵥ ((T.h x)⁻¹ *ᵥ w)) ≠ 0
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩
    (fun j z hz => T.fr_ne j x z hx hz) t ht
  exact ⟨a, ha, h₁, h₂, hv⟩

theorem rootVal_of_isThetaPt {k : Fin F.n} (T : ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ))
    (hun : IsNormUn T (un k)) (x : Fin T.m → ℂ) (hx : x ∈ T.co ⁻¹' (M.X k).dom) (a : ℂ) (ha : a ≠ 0)
    (y : FrPt Xo c (CAt σ)) (hy : IsThetaPt T x a y) :
    RootVal (unfOf e F M un) y
      ((normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h x).det / a ^ 2) := by
  obtain ⟨κ, hκ, hθ⟩ := hun ⟨T.co x, hx⟩
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hκ hθ
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC (T.norm _ hx).1.ne_zero (by rw [← hκ, h0]; simp)
  let t₀ : ℂˣ := Units.mk0 (a / κ) (div_ne_zero ha k1)
  have hb := GlobalTheory.frBor_of_isThetaPt GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ g e F r M k T x hx κ
    (show (CAt σ)ˣ from t₀) (un k ⟨T.co x, hx⟩) y hθ (by
      have : a / κ * κ = a := div_mul_cancel₀ a k1
      show IsThetaPt T x (a / κ * κ) y
      rwa [this])
  refine ⟨k, ⟨T.co x, hx⟩, _, hb, ?_⟩
  have hk : kch (Dw := Dw) (S := ℂ) (fun i => Option.elim i t₀ (fun _ => 1)) = (t₀ ^ 2)⁻¹ := by
    rw [kch_eq]
    simp
  refine Eq.trans ?_ (congrArg Units.val hk).symm
  rw [← hκ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0]
  field_simp

end

theorem continuousOn_rootVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (T : ∀ k, ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → (∀ k, IsNormUn (T k) (un k)) → FramesOK e F M un → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (ρ : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → (∀ b ∈ B, RootVal (unfOf e F M un) (y b) (ρ b)) → ContinuousOn ρ B := by
  intro E _ _ _ H Dw l Xo c σ g e F r M T un hσ hM hξ hun hok A _ _ yA m B φ y ρ hB hφ hy hρ b₀ hb₀
  obtain ⟨B', k, P, hB', hb', hsub, hP, hd⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨x, hx, hxc⟩ :=
    GlobalTheory.FrameLiftAt.exists_frame_lift E H Dw l Xo c σ g e F r M k (T k) hσ hM hξ m B' P hB' hP b₀ hb'
  have h₁ : ∀ b ∈ B', ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt (T k) (x b) a (y b) := fun b hb =>
    exists_isThetaPt_of_adapted (T k) (x b) (hx b hb).1 (y b) (by rw [(hx b hb).2]; exact (hd b hb).1)
      (by rw [(hx b hb).2]; exact (hd b hb).2)
  choose! a ha hθ using h₁
  have hac : ContinuousAt a b₀ :=
    GlobalTheory.ThetaScalar.continuousAt_scalar E H Dw l Xo c σ g e F r M k (T k) A yA m B' φ y P x a hB'
      (fun t => (hφ t).mono hsub) (fun b hb => hy b (hsub hb)) hP
      (fun b hb => ⟨(hx b hb).1, (hx b hb).2, hθ b hb⟩) b₀ hb' hxc
  have hO : IsOpen ((T k).co ⁻¹' (M.X k).dom) := (FourierCoefficientDomain.isOpen_dom _).preimage (T k).co.continuous
  have hh : ContinuousAt (T k).h (x b₀) := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    ((T k).hol i j).1.continuousOn.continuousAt (hO.mem_nhds (hx b₀ hb').1)
  have hdet : ContinuousAt (fun b => ((T k).h (x b)).det) b₀ :=
    (continuous_id.matrix_det.continuousAt).comp (ContinuousAt.comp hh hxc)
  have hq : ContinuousAt (fun b => (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) *
      ((T k).h (x b)).det / a b ^ 2) b₀ :=
    (continuousAt_const.mul hdet).div (hac.pow 2) (pow_ne_zero 2 (ha b₀ hb'))
  refine (hq.congr ?_).continuousWithinAt
  filter_upwards [hB'.mem_nhds hb'] with b hb
  exact rootVal_unique E H Dw l Xo c σ g e F r M un hσ hM hξ hok (y b) _ _
    (rootVal_of_isThetaPt (T k) un (hun k) (x b) (hx b hb).1 (a b) (ha b hb) (y b) (hθ b hb)) (hρ b (hsub hb))

end GlobalTheory.KeyFourth
end

