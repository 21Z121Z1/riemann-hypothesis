import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushEquivPolPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationSpans
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isLieBasis_of_local_restrict : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G], Smooth G.hom →
    ∀ (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → (epsR R ⟶ G)),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) →
    ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T), (IsLocalRing.maximalIdeal T).comap g = p →
    ∀ (G' : Over (Sp T)) [GrpObj G'] (ψ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) ψ →
    ∀ v : Fin n → (epsR T ⟶ G'), (∀ i, GlobalTheory.IsVecOver g ψ (w i) (v i)) → IsLieBasis v := by
  intro R _ G _ hsm p _ n w hw T _ _ g hg G' _ ψ h v hv
  haveI : Smooth G.hom := hsm
  let φp : Localization.AtPrime p →+* T := IsLocalization.lift (M := p.primeCompl) (g := g)
    (fun x => not_not.1 fun h0 => x.2 (hg ▸ (show x.1 ∈ (IsLocalRing.maximalIdeal T).comap g from h0)))
  have hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = g := IsLocalization.lift_comp _
  have hsp : spMap g = spMap φp ≫ Chart.fB R (Localization.AtPrime p) := by
    show Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom φp) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ := hsp ▸ h
  have hG := Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'
  have : Smooth (Chart.Gp (G := G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance
  have hb : IsLieBasis (G := Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by
    refine hw (Chart.Gp (G := G) p) (pullback.fst G.hom (Chart.fB R (Localization.AtPrime p)))
      (isGrpPullback_pullback G (Chart.fB R (Localization.AtPrime p))) _ fun i => ?_
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w i))
    simp only [Chart.pushR_left, Over.comp_left] at e
    exact e
  refine Chart.isLieBasis_baseChange φp hG hb fun j => ?_
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hv j, Category.assoc]
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))
    simp only [Chart.pushR_left, Over.comp_left] at e
    rw [e, ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (Chart.dualMapR g)) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]
    rw [show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) =
      (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]
    show Spec.map (CommRingCat.ofHom (algebraMap T (DualNumber T))) ≫ Spec.map (CommRingCat.ofHom φp) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsLocalizationLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieFrameLoc

theorem scaleD_scaleD {R : Type} [CommRing R] {G : Over (Sp R)} (a b : R)
    (y : Chart.sp (R₀ := R) (DualNumber R) ⟶ G) :
    Chart.spMap (Chart.scaleD a) ≫ Chart.spMap (Chart.scaleD b) ≫ y = Chart.spMap (Chart.scaleD (a * b)) ≫ y := by
  rw [← Category.assoc, Chart.spMap_comp]
  congr 2
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleD]
  · simp only [Chart.scaleD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul]
    ring

theorem isLieBasis_scale {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {u : Fin n → (epsR R ⟶ G)}
    (hu : IsLieBasis u) (a : Fin n → Rˣ)
    (ht : ∀ i, IsTangent (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) :
    IsLieBasis (fun i => (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) := by
  have key : ∀ c : Fin n → R, Chart.prodPts c (fun i => Chart.spMap (Chart.scaleD (a i : R)) ≫ u i) =
      Chart.prodPts (fun i => c i * a i) u := fun c => by
    unfold Chart.prodPts
    exact congrArg List.prod (congrArg List.ofFn (funext fun i => scaleD_scaleD _ _ _))
  refine ⟨ht, fun w hw => ?_⟩
  obtain ⟨c, hc, huniq⟩ := hu.2 w hw
  refine ⟨fun i => c i * ↑(a i)⁻¹, ?_, fun c' hc' => ?_⟩
  · rw [Chart.isLieComb_iff] at hc ⊢
    rw [key, hc]
    congr 1
    funext i
    simp [mul_assoc]
  · replace hc' := (Chart.isLieComb_iff _ _ _).mp hc'
    rw [key] at hc'
    have := huniq _ ((Chart.isLieComb_iff _ _ _).mpr hc')
    funext i
    have hi := congrFun this i
    rw [← hi]
    simp [mul_assoc]

end GlobalTheory.LieFrameLoc

open GlobalTheory.LieFrameLoc in
open scoped CategoryTheory.Obj in

theorem GlobalTheory.exists_tangent_isLieBasis_atPrime : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → ∀ (p : Ideal R) [p.IsPrime],
    ∃ (n : ℕ) (w : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (w i)) ∧
      (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) := by
  intro R _ G _ hsm p _
  haveI := hsm
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  have hGp : Smooth (Chart.Gp (G := G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance
  obtain ⟨n, u, hu⟩ := Chart.exists_isLieBasis (Chart.Gp (G := G) p) hGp
  have lift : ∀ i, ∃ q ∈ p.primeCompl, ∃ w : epsR R ⟶ G, IsTangent w ∧
      Chart.resP p w = Chart.spMap (Chart.scaleD (algebraMap R (Localization.AtPrime p) q)) ≫ u i := by
    intro i
    have hT : Chart.TanS (Chart.pushR G (u i)) := (Chart.isTan_iff_tanS p (u i)).mp ((Chart.isTan_iff _).mpr (hu.1 i))
    obtain ⟨q, hq, w, hw, he⟩ := Chart.tan_prime_lift p hT
    refine ⟨q, hq, w, (Chart.isTan_iff _).mp hw, Chart.pushR_inj G ?_⟩
    rw [Chart.pushR_resP, he, Chart.pushR_spMap]
    congr 2
  choose q hq w hw hres using lift
  refine ⟨n, w, hw, fun G' _ ψ hψ v hv => ?_⟩
  let a : Fin n → (Localization.AtPrime p)ˣ := fun i => (IsLocalization.map_units _ ⟨q i, hq i⟩).unit
  have hres' : ∀ i, Chart.resP p (w i) = Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i := hres
  have htan : ∀ i, IsTangent (Chart.resP p (w i)) := fun i =>
    (Chart.isTan_iff _).mp ((Chart.isTan_iff_tanS p _).mpr (by
      rw [Chart.pushR_resP]; exact Chart.tanS_restrict _ ((Chart.isTan_iff _).mpr (hw i))))
  have hbasis : IsLieBasis (G := Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by
    have e : (fun i => Chart.resP p (w i)) = fun i => Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i :=
      funext hres'
    rw [e]
    exact isLieBasis_scale hu a fun i => hres' i ▸ htan i
  let φp : Localization.AtPrime p →+* Localization.AtPrime p := RingHom.id _
  have hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = algebraMap R (Localization.AtPrime p) := RingHom.id_comp _
  have hsp : spMap (algebraMap R (Localization.AtPrime p)) = spMap φp ≫ Chart.fB R (Localization.AtPrime p) := by
    show Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) = Spec.map (CommRingCat.ofHom φp) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ := hsp ▸ hψ
  have hG := Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'
  have hv' : ∀ j, (v j).left ≫ ψ = spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ (w j).left := hv
  refine Chart.isLieBasis_baseChange φp hG hbasis fun j => ?_
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hv' j, Category.assoc]
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))
    simp only [Chart.pushR_left, Over.comp_left] at e
    rw [e, ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p)))) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]
    rw [show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) =
      (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]
    show Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p)))) ≫
        Spec.map (CommRingCat.ofHom φp) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [φp, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

abbrev phiTP (a : Fin p) : letI := H.starRing; (pointA hv ε i X true).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiTQ (b : Fin q) : letI := H.starRing; (pointA hv ε i X false).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A false) hv ε i (X.lin (Sum.inr b))

variable [IsAlgClosed C] [CharZero C]

omit [NumberField K] in

theorem pairT_patT_gram {T T' : PAT H (Sp (𝓞 K))} {f f' : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)
    (hf' : Serre.IsLinearHom T.t.act T'.t.act f') {g : 𝓞 E}
    (h : LamEq T'.t.PP.L f f' T.t.PP.L (T.t.act.act g) (𝟙 _)) : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i T').A ε (patT hv ε i hf s) (patT hv ε i hf' t) =
      pairT (patPoint hv ε i T).A ε ((patPoint hv ε i T).actT g s) t := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f' := hf'.isMonHom
  haveI := (patAct T).hom g
  intro s t
  have e := pairT_homT_of_lamEq (X := T.pol) (Y := T.pol) (A := T'.pol) (B := T.pol) hv ε (embO hv i) (patAct T) (patAct T)
    (patAct T') (patAct T) f f' ((patAct T).act g) (𝟙 _) h s t
  rw [homT_act, homT_id] at e
  exact e

theorem pairT_patT_orth (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {A A' B : PAT H (Sp (𝓞 K))} {m m' : ℕ}
    (hA : HasType H A.t.act ρ m 0) (hA' : HasType H A'.t.act ρ 0 m') {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hf' : Serre.IsLinearHom A'.t.act B.t.act f') : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i B).A ε (patT hv ε i hf s) (patT hv ε i hf' t) = 0 := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A.pol.A) (N := B.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A'.pol.A) (N := B.pol.A) f' := hf'.isMonHom
  haveI : IsMonHom (1 : A'.pol.A ⟶ A.pol.A) := LamF.IsogSum.isMonHom_of_points _ fun T a b => by
    simp only [MonObj.comp_one, _root_.mul_one]
  intro s t
  have e := pairT_homT_of_lamEq (X := A.pol) (Y := A'.pol) (A := B.pol) (B := A.pol) hv ε (embO hv i) (patAct A)
    (patAct A') (patAct B) (patAct A) f f' (𝟙 _) 1 (lamEq_one hρ A A' B hA hA' hf hf') s t
  rw [homT_one, LinearMap.zero_apply, map_zero] at e
  exact e

theorem tateModule_gram_relations_blocks_orthogonal {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTP hv ε i X b t) =
      pairT (pointA hv ε i X true).A ε ((pointA hv ε i X true).actT (gP a b) s) t) ∧
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTQ hv ε i X a s) (phiTQ hv ε i X b t) =
      pairT (pointA hv ε i X false).A ε ((pointA hv ε i X false).actT (gQ a b) s) t) ∧
    ∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTQ hv ε i X b t) = 0 :=
  ⟨fun a b => pairT_patT_gram (T := X.A true) hv ε i (X.lin (.inl a)) (X.lin (.inl b)) ((lamEq_of_isGram X h).1 a b),
    fun a b => pairT_patT_gram (T := X.A false) hv ε i (X.lin (.inr a)) (X.lin (.inr b)) ((lamEq_of_isGram X h).2 a b),
    fun a b => pairT_patT_orth (A := X.A true) (A' := X.A false) hv ε i X.ρ_sq X.typeP X.typeM (X.lin (.inl a))
      (X.lin (.inr b))⟩

end At

theorem exists_inverse_tateModule_sum_up_to_integer (X : CMObj H K ρ σ₁ p q) : letI := H.starRing
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O]
      [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C),
      ∃ (ψ : Fin p → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X true).T))
        (ψ' : Fin q → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X false).T)),
        (∀ t, ∑ k, phiTP hv ε i X k (ψ k t) + ∑ k, phiTQ hv ε i X k (ψ' k t) = N • t) ∧
        ∀ (s : Fin p → (pointA hv ε i X true).T) (s' : Fin q → (pointA hv ε i X false).T),
          (∀ l, ψ l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s l) ∧
          ∀ l, ψ' l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s' l := by
  letI := H.starRing
  haveI hP : ∀ i, IsMonHom (M := (X.A true).pol.A) (N := X.B.pol.A) (phiP X i) := fun i => (X.lin (.inl i)).isMonHom
  haveI hQ : ∀ i, IsMonHom (M := (X.A false).pol.A) (N := X.B.pol.A) (phiQ X i) := fun i => (X.lin (.inr i)).isMonHom
  obtain ⟨N, ψ, ψ', hN, hψ, hψ', h1, h2⟩ := exists_inverse X
  exact ⟨N, hN, fun ℓ _ C _ v O _ _ hv ε i => ⟨_, _, homT_inverse (B := X.B.pol) (A := (X.A true).pol)
    (A' := (X.A false).pol) hv ε (embO hv i) (patAct X.B) (patAct (X.A true)) (patAct (X.A false)) (phiP X) (phiQ X)
    ψ ψ' h1 h2⟩⟩

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q) [IsAlgClosed C] [CharZero C]

theorem sumT_injective : letI := H.starRing
    Function.Injective fun z : (Fin p → (pointA hv ε i X true).T) × (Fin q → (pointA hv ε i X false).T) =>
      ∑ k, phiTP hv ε i X k (z.1 k) + ∑ k, phiTQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', -, h2⟩ := h ℓ C v O hv ε i
  have key : ∀ (P : Point ℓ v O (𝓞 E)) (x y : P.T), N • x = N • y → x = y := fun P x y e => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], ← Nat.cast_smul_eq_nsmul ℤ_[ℓ]] at e
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') e
  exact fun z z' e => Prod.ext
    (funext fun l => key _ _ _ (((h2 z.1 z.2).1 l).symm.trans ((congrArg (ψ l) e).trans ((h2 z'.1 z'.2).1 l))))
    (funext fun l => key _ _ _ (((h2 z.1 z.2).2 l).symm.trans ((congrArg (ψ' l) e).trans ((h2 z'.1 z'.2).2 l))))

include hv ε i in
theorem gram_det_of_emb {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  letI := H.starRing
  obtain ⟨N, hN, hI⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, -⟩ := hI ℓ C v O hv ε i
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  have hg : ∀ b, 0 < (pointA hv ε i X b).A.g := fun b => (dims X).2.2.trans_eq ((dims X).1 b).symm
  have hi := sumT_injective hv ε i X
  refine ⟨det_ne_zero_of_inverse hN (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
      (hg true) (phiTP hv ε i X) (phiTQ hv ε i X) gP hP hO (fun t => ⟨_, _, h1 t⟩) fun s hs => ?_,
    det_ne_zero_of_inverse hN (A := pointA hv ε i X false) (A' := pointA hv ε i X true) (B := pointB hv ε i X)
      (hg false) (phiTQ hv ε i X) (phiTP hv ε i X) gQ hQ (fun a b s t => ?_)
      (fun t => ⟨_, _, (add_comm _ _).trans (h1 t)⟩) fun s hs => ?_,
    star_gram (A := pointA hv ε i X true) (B := pointB hv ε i X) (hg true) (phiTP hv ε i X) gP hP,
    star_gram (A := pointA hv ε i X false) (B := pointB hv ε i X) (hg false) (phiTQ hv ε i X) gQ hQ⟩
  · exact congrArg Prod.fst (@hi (s, 0) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))
  · exact ((isAlt_pairT (pointB hv ε i X).A ε).neg_eq _ _).symm.trans (neg_eq_zero.2 (hO b a t s))
  · exact congrArg Prod.snd (@hi (0, s) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))

variable [Algebra ℤ_[ℓ] C]

theorem gram_V {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVP hv ε i X b y) =
      (pointA hv ε i X true).pairV ((pointA hv ε i X true).actV (gP a b) x) y) ∧
    (∀ a b x y, (pointB hv ε i X).pairV (phiVQ hv ε i X a x) (phiVQ hv ε i X b y) =
      (pointA hv ε i X false).pairV ((pointA hv ε i X false).actV (gQ a b) x) y) ∧
    ∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVQ hv ε i X b y) = 0 := by
  letI := H.starRing
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  refine ⟨fun a b x y => ?_, fun a b x y => ?_, fun a b x y => ?_⟩
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X true) (g₂ := LinearMap.id) (hP a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X false) (g₂ := LinearMap.id) (hQ a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointB hv ε i X) (g₁ := 0) (g₂ := 0)
      (fun s t => (hO a b s t).trans (map_zero _).symm) x y
    rw [LinearMap.baseChange_zero, LinearMap.baseChange_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero] at e
    exact e

theorem sumV_bijective : letI := H.starRing
    Function.Bijective fun z : (Fin p → (pointA hv ε i X true).V) × (Fin q → (pointA hv ε i X false).V) =>
      ∑ k, phiVP hv ε i X k (z.1 k) + ∑ k, phiVQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, h2⟩ := h ℓ C v O hv ε i
  exact bijective_of_inverse (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
    (phiTP hv ε i X) (phiTQ hv ε i X) hN ψ ψ' h1 h2

end At

theorem gram_det (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  obtain ⟨ε⟩ : Nonempty (Eps 2 ℂ_[2]) := inferInstance
  exact gram_det_of_emb (PadicComplexInt.integers 2) ε (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[2])).toRingHom X h

theorem exists_patT_equiv {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] [IsAlgClosed C] [CharZero C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) {C' : Type} [Field C']
    {v' : Valuation C' ℝ≥0} {O' : Type} [CommRing O'] [Algebra O' C'] [IsAlgClosed C'] [CharZero C']
    (hv' : v'.Integers O') (ε' : Eps ℓ C') (i' : K →+* C') : letI := H.starRing
    ∃ e : ∀ T : PAT H (Sp (𝓞 K)), (patPoint hv ε i T).T ≃ₗ[ℤ_[ℓ]] (patPoint hv' ε' i' T).T,
      (∀ T a t, e T ((patPoint hv ε i T).actT a t) = (patPoint hv' ε' i' T).actT a (e T t)) ∧
      ∀ (T T' : PAT H (Sp (𝓞 K))) (f : T.t.G ⟶ T'.t.G) (hf : Serre.IsLinearHom T.t.act T'.t.act f) (t),
        e T' (patT hv ε i hf t) = patT hv' ε' i' hf (e T t) := by
  letI := H.starRing
  have lift : ∀ {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
      (hv : v.Integers O) (i : K →+* C), ∃ κ : AlgebraicClosure K →+* C,
        κ.comp (algebraMap (𝓞 K) (AlgebraicClosure K)) = (algebraMap O C).comp (embO hv i) := by
    intro C _ _ v O _ _ hv i
    letI := i.toAlgebra
    refine ⟨(IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := C)).toRingHom, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_embO, IsScalarTower.algebraMap_apply (𝓞 K) K]
    exact AlgHom.commutes _ _
  obtain ⟨κ, hκ⟩ := lift hv i
  obtain ⟨κ', hκ'⟩ := lift hv' i'
  obtain ⟨e, he⟩ := exists_tateEquiv (Λ := 𝓞 E) hv ε (embO hv i) _ κ hκ
  obtain ⟨e', he'⟩ := exists_tateEquiv (Λ := 𝓞 E) hv' ε' (embO hv' i') _ κ' hκ'
  have key : ∀ (B B' : Out.PolAV (Sp (𝓞 K))) (o : B.OAct (𝓞 E)) (o' : B'.OAct (𝓞 E)) (f : B.A ⟶ B'.A) [IsMonHom f] (t),
      e' B' o' ((e B' o').symm (homT hv ε (embO hv i) o o' f t)) =
        homT hv' ε' (embO hv' i') o o' f (e' B o ((e B o).symm t)) := fun B B' o o' f _ t => by
    rw [← he', (e B' o').symm_apply_eq.2 ((congrArg _ ((e B o).apply_symm_apply t).symm).trans (he B B' o o' f _).symm)]
  refine ⟨fun T => (e T.pol (patAct T)).symm.trans (e' T.pol (patAct T)), fun T a t => ?_, fun T T' f hf t => ?_⟩
  · haveI := (patAct T).hom a
    have h := key T.pol T.pol (patAct T) (patAct T) ((patAct T).act a) t
    rw [homT_act, homT_act] at h
    exact h
  · haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
    exact key T.pol T'.pol (patAct T) (patAct T') f t

example (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) (ℓ : ℕ) [Fact ℓ.Prime] (ε : Eps ℓ ℂ_[ℓ]) (i : K →+* ℂ_[ℓ]) :
    letI := H.starRing; letI := algPadicField ℓ
    ∀ a b x y, (pointB (PadicComplexInt.integers ℓ) ε i X).pairV (phiVP (PadicComplexInt.integers ℓ) ε i X a x)
      (phiVQ (PadicComplexInt.integers ℓ) ε i X b y) = 0 :=
  letI := algPadicField ℓ
  (gram_V (PadicComplexInt.integers ℓ) ε i X h).2.2

end Object

end GlobalTheory.GramAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauPeriodValNegCubicalRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TauNeg

theorem val_tau_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (D.tau (-a) (-b)) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c (-a)) (toUnit (TK R) ≫ D.c b) * (cubV D.cub z J (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c (-b)) (toUnit (TK R) ≫ D.c (-a)))⁻¹ := by
  intro R _ _ D hB a b z J hJ
  have xadd : ∀ u v : D.X, toUnit (TK R) ≫ D.c (u + v) = (toUnit (TK R) ≫ D.c u) * (toUnit (TK R) ≫ D.c v) := by
    intro u v; rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have x0 : toUnit (TK R) ≫ D.c 0 = 1 := by
    have h := xadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have C := isCub_cubV D.cub hJ
  have B : ∀ u u' w v : D.X, u + u' = w → val (D.tau w v) (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) =
      val (D.tau u v) (𝟙 _) z J * val (D.tau u' v) (𝟙 _) z J := by
    rintro u u' w v rfl
    have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
    have hc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 u u' v)) (𝟙 _) z J =
        cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) := by
      refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
      rw [Category.id_comp, Category.id_comp, Category.id_comp]
    rw [← hc]
    exact h
  have sym : ∀ u v : D.X, val (D.tau u v) (𝟙 _) z J = val (D.tau v u) (𝟙 _) z J := by
    intro u v
    simp only [DegPre.tau, val_mul hJ, val_inv]
    rw [add_comm u v, mul_right_comm (val (D.psi (v + u)) (𝟙 _) z J)]
  have T0 : ∀ v : D.X, val (D.tau 0 v) (𝟙 _) z J = 1 := by
    intro v
    have h := B 0 v v v (zero_add v)
    rw [x0, C.face, _root_.mul_one] at h
    exact (mul_eq_right.1 h.symm)
  have e1 := B a (-a) 0 b (add_neg_cancel a)
  have e2 := B b (-b) 0 (-a) (add_neg_cancel b)
  rw [T0, _root_.one_mul] at e1 e2
  rw [e1, e2, sym b (-a), sym (-b) (-a)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslates
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSym

theorem lam_mul_left {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) {Y : Over S} (a a' x : Y ⟶ A) : lam c (a * a') x = lam c a x + lam c a' x := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have h := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  simpa only [e] using (isAdditive_iff hP).1 h Y a a' x

theorem pull_mul_add_pull_mul_inv : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (Y : Over S) (x a : Y ⟶ A), GlobalTheory.CechPic.pull (x * a).left c + GlobalTheory.CechPic.pull (x * a⁻¹).left c = 2 • GlobalTheory.CechPic.pull (x).left c + GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull (a⁻¹).left c - 2 • GlobalTheory.CechPic.pull ((1 : Y ⟶ A)).left c := by
  intro S _ A _ hA c Y x a
  haveI := hA.comm
  have h := lam_mul_left hA c a a⁻¹ x
  rw [mul_inv_cancel, lam_one_left, lam_comm c a x, lam_comm c a⁻¹ x, lam, lam] at h
  rw [← sub_eq_zero, h]
  abel

end GlobalTheory.SquareSym
end

