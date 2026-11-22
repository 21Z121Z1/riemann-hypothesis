import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorsFixed

theorem fixed_of_classes_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hB D A G _ _ hG U V _ _ φ _ hc k hk σ hσ hQ x hx
  haveI : CharZero R := hB.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws

  have sq : (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V) ≫ spMap φ =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    show (spMap _ ≫ spMap _) ≫ spMap φ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp, ← spMap_comp]
    congr 1
    ext r
    exact (hc r).symm
  have wx : x.left ≫ pullback.snd G.hom (spMap φ) = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := Over.w x
  have w₁ : (x.left ≫ pullback.fst G.hom (spMap φ)) ≫ G.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, wx, sq]
  let xG : Over.mk (jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R) ⟶ G :=
    Over.homMk (x.left ≫ pullback.fst G.hom (spMap φ)) w₁
  have hxG : xG ^ k = 1 :=
    (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull sq (isGrpPullback_pullback G (spMap φ)) (x := xG) (x' := x) rfl).1 hx

  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  let x₀ : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (gp.1.lift (x.left ≫ pullback.fst G.hom (spMap φ)) (jFK (R := R) (AlgebraicClosure (FractionRing V))) w₁)
      (gp.1.lift_snd _ _ _)
  have e₀ : x₀.left ≫ (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) = x.left ≫ pullback.fst G.hom (spMap φ) :=
    gp.1.lift_fst _ _ _
  have hx₀ : x₀ ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := x₀) e₀).2 hxG

  have hσR : ∀ r : R, σ (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r => by
    rw [hc r, hσ]
  let σ' : AlgebraicClosure (FractionRing V) →ₐ[FractionRing R] AlgebraicClosure (FractionRing V) :=
    ⟨σ.toRingHom, fun a => RingHom.congr_fun
      (IsLocalization.ringHom_ext (nonZeroDivisors R)
        (j := σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))))
        (k := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) (RingHom.ext hσR)) a⟩
  have hσf : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) := RingHom.ext σ'.commutes

  obtain ⟨f, hf, hsurj, hfi, -, -⟩ :=
    GlobalTheory.TorsionIso.torsion_eq hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V)) k hk
  obtain ⟨p, hp⟩ := hsurj x₀ hx₀
  let q := GlobalTheory.TorusExt.qkExt D.tau_bimult σ.toRingHom hσf p
  have hpq : QkExt σ.toRingHom p q := (GlobalTheory.TorusExt.qkExt_iff D.tau_bimult σ.toRingHom hσf p q).2 rfl
  have heq : f q = x₀ := ((hfi p q).2 (hQ p q hpq)).symm.trans hp
  have s₂ : spMap σ.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing V)) =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) := by
    refine (spMap_comp _ _).symm.trans ?_
    exact congrArg spMap hσf
  have wx₀ : x₀.left ≫ A.A.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) := Over.w x₀
  let x' : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (spMap σ.toRingHom ≫ x₀.left) (by rw [Category.assoc, wx₀, s₂]; rfl)
  have hq : QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V))
      (AlgebraicClosure (FractionRing V)) σ' k hk p q x₀ x' hpq rfl).1 ((hf p x₀).2 hp.symm)
  have fix : spMap σ.toRingHom ≫ x₀.left = x₀.left := congrArg (fun z => z.left) (((hf q x').1 hq).trans heq)

  have sV : spMap σ.toRingHom ≫ jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := by
    show spMap _ ≫ spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext v
    exact hσ v
  refine pullback.hom_ext (f := G.hom) (g := spMap φ) ?_ ?_
  · rw [Category.assoc, ← e₀, ← Category.assoc, fix]
  · rw [Category.assoc, wx, sV]

end GlobalTheory.Mum.TorsFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassAtStalkSmulAction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem exists_geomPt_range_eq_singleton (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  refine ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g, ?_⟩
  ext y
  have h := fun t => X.fromSpecResidueField_apply g
    (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) (AlgebraicClosure (X.residueField g)))) t)
  simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
  exact ⟨fun ⟨t, e⟩ => e.symm.trans (h t),
    fun e => ⟨IsLocalRing.closedPoint _, (h _).trans e.symm⟩⟩

theorem exists_geomPt_stalk_over {X' : Scheme.{0}} [IsIntegral X'] {T : Scheme.{0}} (f : T ⟶ X') [Flat f]
    {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (p : T) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec (T.presheaf.stalk p)) (z : Sp Ω ⟶ V),
      y ≫ T.fromSpecStalk p ≫ f = z ≫ ℓ := by
  obtain ⟨p', hp', hfp'⟩ := Flat.generalizingMap f (genericPoint_specializes (f p))
  have hmem : p' ∈ Set.range (T.fromSpecStalk p) := by rw [Scheme.range_fromSpecStalk]; exact hp'
  obtain ⟨d, hd⟩ := hmem
  obtain ⟨Ω, hF, hA, y, hy⟩ := exists_geomPt_range_eq_singleton _ d
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    refine ((genericPoint_spec X').mem_open_set_iff (IsOpenImmersion.isOpen_range ℓ)).mpr ?_
    exact ⟨ℓ (Classical.arbitrary V), trivial, _, rfl⟩
  have hr : Set.range (y ≫ T.fromSpecStalk p ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨t, rfl⟩
    have ht : y t = d := by
      have : y t ∈ Set.range y := ⟨t, rfl⟩
      rw [hy] at this
      exact this
    simp only [Scheme.Hom.comp_apply, ht, hd, hfp']
    exact hgen
  exact ⟨Ω, hF, hA, y, IsOpenImmersion.lift ℓ _ hr, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory.TorsSpec

namespace GlobalTheory.TorsSpec

theorem valAt_comp {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (τ : torsion G n ⟶ torsion G n) (p q : (torsion G n).left) (hq : τ.left p = q) (c : M)
    (h : ValAt G n ℓ w q c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V)
    (hyz : y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ (torsion G n).left.fromSpecStalk p ≫ τ.left ≫ (torsion.ι G n).left = z ≫ w c := by
  subst hq
  have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ.left (x := p)
  have hw : τ.left ≫ (torsion G n).hom = (torsion G n).hom := Over.w τ
  have h1 := h Ω (y ≫ Spec.map (τ.left.stalkMap p)) z (by
    simpa only [Category.assoc, reassoc_of% key, hw] using hyz)
  simpa only [Category.assoc, reassoc_of% key] using h1

theorem class_act : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    (hlin : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a : M) (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w (r • a) → B = A ≫ act.act r)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P : Over.mk t ⟶ G) (r : 𝓞 E)
    (PT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hRT : RT ≫ (torsion.ι G n).left = (P ≫ act.act r).left) (x : Sp K) (cP cR : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = r • cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act hlin K _ _ t P r PT RT hPT hRT x cP cR hcP hcR
  haveI := GrpTangent.etale_torsion G hn
  haveI := mono_torsion_ι G n
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G)) (CartesianMonoidalCategory.toUnit_unique _ _))
  have hτ : (torsion.ι G n ≫ act.act r) ≫ mulN G n = 1 := by
    haveI := act.hom r
    rw [← act_natCast act n, Category.assoc, ← act.mul, mul_comm, act.mul, ← Category.assoc,
      act_natCast act n, hι, Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  obtain ⟨τ, hτι⟩ := exists_lift_torsion n _ hτ
  have hτl : τ.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ (act.act r).left := by
    rw [← Over.comp_left, hτι, Over.comp_left]
  have hPR : PT ≫ τ.left = RT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτl, reassoc_of% hPT, hRT, Over.comp_left]
  have hq : τ.left (PT x) = RT x := by rw [← hPR, Scheme.Hom.comp_apply]
  obtain ⟨Ω, hF, hA, y, z, hyz⟩ := exists_geomPt_stalk_over (torsion G n).hom ℓ (PT x)
  have h1 := hcP Ω y z hyz
  have h2 := valAt_comp G n ℓ w τ (PT x) (RT x) hq cR hcR Ω y z hyz
  rw [hτl, reassoc_of% h1] at h2
  let A : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w cP) (by rw [Category.assoc, hw]; rfl)
  let B : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w (r • cP)) (by rw [Category.assoc, hw]; rfl)
  have h3 := congrArg (fun q => q.left) (hlin Ω z cP r A B rfl rfl)
  simp only [A, B, Over.homMk_left, Over.comp_left] at h3
  exact (hun Ω z _ _ (h3.trans ((Category.assoc _ _ _).trans h2))).symm

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionLocal

lemma comp_pow_overScheme_grpObj {A T : Over (Sp ℂ)} [GrpObj A] (f : T ⟶ A) (g : A ⟶ A) :
    ∀ n : ℕ, f ≫ g ^ n = (f ≫ g) ^ n
  | 0 => by simp [MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj f g n]

theorem locally_eq_const_of_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  intro A _ hA N hN T x hx t
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit ((N : ℂ)) := (Nat.cast_ne_zero.mpr (by omega)).isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨-, hfin, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective (Sp ℂ) A N hA hunit
  set f : A ⟶ A := (𝟙 A) ^ N with hf
  have hTu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  have hxf : x.left ≫ f.left = T.hom ≫ η[A].left := by
    have h1 : x ≫ f = toUnit T ≫ η[A] := by
      rw [hf, comp_pow_overScheme_grpObj, Category.comp_id, hx]; rfl
    have h2 := congrArg (fun h => h.left) h1
    simpa [hTu] using h2
  haveI : IsFinite f.left := hfin
  haveI : Etale f.left := het
  haveI := hA.smooth
  have hη : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  have hfw : f.left ≫ A.hom = A.hom := Over.w f
  have hpt : T.hom t = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  set a := x.left t with ha_def
  have hfa : f.left a = η[A].left (IsLocalRing.closedPoint ℂ) := by
    rw [ha_def, ← Scheme.Hom.comp_apply, hxf, Scheme.Hom.comp_apply, hpt]
  have he : IsClosed ({η[A].left (IsLocalRing.closedPoint ℂ)} : Set A.left) :=
    ((pointEquivClosedPoint A.hom) ⟨η[A].left, hη⟩).2
  haveI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have ha : IsClosed ({a} : Set A.left) := by
    rw [isClosed_singleton_iff_locallyOfFiniteType]
    have h1 : LocallyOfFiniteType (A.left.fromSpecResidueField (f.left a)) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp (hfa ▸ he)
    have h2 : LocallyOfFiniteType (Spec.map (f.left.residueFieldMap a)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.FiniteType.of_finite (residueFieldMap_finite_of_locallyQuasiFinite f.left a)
    have h3 : LocallyOfFiniteType (A.left.fromSpecResidueField a ≫ f.left) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; infer_instance
    exact locallyOfFiniteType_of_comp _ f.left
  let y0 : Sp ℂ ⟶ A.left := pointOfClosedPoint A.hom a ha
  have hy0 : y0 ≫ A.hom = 𝟙 _ := pointOfClosedPoint_comp A.hom a ha
  let y : 𝟙_ (Over (Sp ℂ)) ⟶ A := Over.homMk y0 (by simpa using hy0)
  have hy0f : y0 ≫ f.left = η[A].left := by
    refine ext_of_apply_closedPoint_eq A.hom ?_ hη ?_
    · rw [Category.assoc, hfw, hy0]
    · show f.left (pointOfClosedPoint A.hom a ha (IsLocalRing.closedPoint ℂ)) = _
      exact (congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)).trans hfa
  have hg : x.left ≫ f.left = (T.hom ≫ y0) ≫ f.left := by
    rw [hxf, Category.assoc, hy0f]
  have hψ := Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)
  set ψ := Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
  have hr : (residueFieldIsoBase A.hom a ha).inv ≫ x.left.residueFieldMap t = ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, SpecMap_residueFieldIsoBase_inv]
    erw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    rw [Over.w x]
  have k : T.left.fromSpecResidueField t ≫ x.left = T.left.fromSpecResidueField t ≫ T.hom ≫ y0 := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← hψ]
    simp only [y0, pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp]
    rw [← hr, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let g : T.left ⟶ pullback f.left f.left := pullback.lift x.left (T.hom ≫ y0) hg
  have kg : T.left.fromSpecResidueField t ≫ g =
      (T.left.fromSpecResidueField t ≫ x.left) ≫ pullback.diagonal f.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, k]
  refine ⟨g ⁻¹ᵁ (pullback.diagonal f.left).opensRange, y, ?_, ?_⟩
  · show g t ∈ Set.range (pullback.diagonal f.left)
    have hk := congrArg (fun h => h (IsLocalRing.closedPoint (T.left.residueField t))) kg
    refine ⟨_, ((Scheme.Hom.comp_apply _ _ _).symm.trans hk.symm).trans
      ((Scheme.Hom.comp_apply _ _ _).trans ?_)⟩
    exact congrArg g (Scheme.fromSpecResidueField_apply t _)
  · set U := g ⁻¹ᵁ (pullback.diagonal f.left).opensRange
    have hle : Set.range (U.ι ≫ g) ⊆ Set.range (pullback.diagonal f.left) := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact u.2
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f.left) (U.ι ≫ g) hle
    have h1 := congrArg (· ≫ pullback.fst f.left f.left) hl
    have h2 := congrArg (· ≫ pullback.snd f.left f.left) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, g,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    show U.ι ≫ x.left = U.ι ≫ T.hom ≫ y0
    rw [← h1, h2]

end GlobalTheory.TorsionLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtTrans

theorem ptTrans : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  intro V V' _ _ _ _ K _ _ _ A A' P₀ a a' h h' m x hx
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let e : TFK (R := V) K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V) K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let e' : TFK (R := V') K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V') K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let Φ : (T ⟶ P₀.A) →* (TFK (R := V) K ⟶ A.A) := (preHom e).comp (pushHom h T)
  let Φ' : (T ⟶ P₀.A) →* (TFK (R := V') K ⟶ A'.A) := (preHom e').comp (pushHom h' T)
  have hΦ : ∀ u : T ⟶ P₀.A, (Φ u).left = u.left ≫ a := fun u => by
    simp [Φ, e, preHom, pushHom, pushPt]
  have hΦ' : ∀ u : T ⟶ P₀.A, (Φ' u).left = u.left ≫ a' := fun u => by
    simp [Φ', e', preHom, pushHom, pushPt]
  have inj : Function.Injective Φ := fun u v huv => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← hΦ, ← hΦ, huv]
    · rw [Over.w u, Over.w v]
  have hsq : x.left ≫ A.A.hom = 𝟙 (Sp K) ≫ spMap (algebraMap (FractionRing V) K) := by
    rw [Over.w x, Category.id_comp]; rfl
  let w : T ⟶ P₀.A := Over.homMk (h.1.lift x.left (𝟙 _) hsq) (by simp [T])
  have hw : Φ w = x := by
    apply Over.OverMorphism.ext
    rw [hΦ]
    simp [w]
  have hwm : w ^ m = 1 := by
    apply inj
    rw [map_pow, hw, hx, map_one]
  refine ⟨w.left, Φ' w, ?_, ?_, ?_, ?_⟩
  · simpa [T] using Over.w w
  · rw [← hΦ, hw]
  · rw [hΦ']
  · rw [← map_pow, hwm, map_one]

end GlobalTheory.PtTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OmRes

variable {R : Type} [CommRing R]

theorem val_map_coc {X : Scheme.{0}} {s : X ⟶ Sp R} (E E' : SqExt R) (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B)
    (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (a : Thick.triv E.C y hy ⟶ Thick.triv E'.C y' hy') (ha : ∀ c, a.φ c = φ c)
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Z1 (O (dp0 R) s)) :
    ∃ b : E'.B, E'.val y' hy' f = φ (E.val y hy f) + (ev f a : E'.C) - E'.i b := by
  have e₀ : spMap (φ₀ : E.B →+* E'.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
      spMap (E'.π : E'.C →+* E'.B) ≫ y' := by
    rw [← e, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ := E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') e₀
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ Thick.triv E'.B _ (E'.red_w hy') := Thick.trivHom φ₀ e₀
  have k1 := ev_sq f a (E'.idHom hy') (E.idHom hy) Φ ha
  have k2 := ev_sq f b (E'.secHom (E'.red_w hy') E'.i E'.π_i) (E.secHom (E.red_w hy) E.i E.π_i)
    Φ fun c ↦ (hi c).symm
  refine ⟨ev f b, ?_⟩
  rw [SqExt.val_apply, SqExt.val_apply, map_sub]
  have k1' : (ev f a : E'.C) + (ev f (E'.idHom hy') : E'.C) = φ (ev f (E.idHom hy)) + (ev f Φ : E'.C) := k1
  have k2' : E'.i (ev f b) + (ev f (E'.secHom (E'.red_w hy') E'.i E'.π_i) : E'.C) =
    φ (ev f (E.secHom (E.red_w hy) E.i E.π_i)) + (ev f Φ : E'.C) := k2
  linear_combination k2' - k1'

attribute [local instance] cotOp cotCentral cotTower

variable {D D' : Type} [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R D']

def rho (φ : D →ₐc[R] D') : (cotExt R D).C →ₐ[R] (cotExt R D').C := TrivSqZeroExt.map (cotMap φ)

theorem cotSnd_cotPt (a : D) : cotSnd R D (cotPt R D a) = dUnit R a := by
  simp [cotSnd, cotPt, TrivSqZeroExt.algebraMap_eq_inl, dUnit]

theorem cotSnd_rho (φ : D →ₐc[R] D') (c : (cotExt R D).C) : cotSnd R D' (rho φ c) = cotMap φ (cotSnd R D c) :=
  TrivSqZeroExt.snd_map _ _

theorem rho_cotPt (φ : D →ₐc[R] D') (a : D) : rho φ (cotPt R D a) = cotPt R D' (φ a) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (TrivSqZeroExt.fst_map _ _).trans ?_
    simp [cotPt, TrivSqZeroExt.algebraMap_eq_inl]
  · exact (cotSnd_rho φ _).trans (by rw [cotSnd_cotPt, cotMap_d]; exact (cotSnd_cotPt _).symm)

theorem cotVal_map {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (φ : D →ₐc[R] D') (y : Pt X D) :
    cotVal f (spOver (φ : D →ₐ[R] D') ≫ y) =
      cotMap φ (cotVal f y) + dUnit R (fv f D D' (φ : D →ₐ[R] D') y) := by
  let z : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  let z' : Pt X (cotExt R D').C := spOver (cotPt R D') ≫ spOver (φ : D →ₐ[R] D') ≫ y
  have e : spMap (rho φ : (cotExt R D).C →+* (cotExt R D').C) ≫ z.left = z'.left := by
    change spMap _ ≫ spMap _ ≫ y.left = spMap _ ≫ spMap _ ≫ y.left
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext (rho_cotPt φ)
  let a : trivAt z ⟶ trivAt z' := Thick.trivHom (rho φ) e
  obtain ⟨b, hb⟩ := val_map_coc (cotExt R D) (cotExt R D') (rho φ) (AlgHom.id R R)
    (fun c ↦ (TrivSqZeroExt.fst_map _ _).symm) (fun r ↦ TrivSqZeroExt.map_inl _ _) z.left z.w z'.left z'.w a
    (fun _ ↦ rfl) e f
  have k : rho φ (fv f D _ (cotPt R D) y) + (ev f a : (cotExt R D').C) =
      cotPt R D' (fv f D D' (φ : D →ₐ[R] D') y) + fv f D' _ (cotPt R D') (spOver (φ : D →ₐ[R] D') ≫ y) :=
    ev_sq f (trivMap (cotPt R D) y) a (trivMap (φ : D →ₐ[R] D') y) (trivMap (cotPt R D') _) (rho_cotPt φ)
  have h0 : cotSnd R D' ((cotExt R D').i b) = 0 := rfl
  change cotSnd R D' ((cotExt R D').val z'.left z'.w f - _) =
    cotMap φ (cotSnd R D ((cotExt R D).val z.left z.w f - _)) + _
  rw [← cotSnd_rho, ← cotSnd_cotPt, ← map_add, ← sub_zero (cotSnd R D' (_ + _)), ← h0, ← map_sub, hb, map_sub (rho φ)]
  congr 1
  linear_combination k

theorem cotMap_res_om (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    cotMap (G.res n) (d.om (n + 1)) = d.om n := by
  have h := cotVal_map d.f (G.res n) (t.y (n + 1))
  rw [t.res n, d.res n] at h
  rw [Dat.om, Dat.om, h, map_sub, cotMap_d]
  simp only [dUnit, map_sub]
  abel

end GlobalTheory.PtExt.OmRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialEvaluationsOfMemKernelSymmetricPairStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.KerAxes.triv_of_memKL_pair | exact GlobalTheory.KerAxes.triv_of_memKL_pair | (intros; apply GlobalTheory.KerAxes.triv_of_memKL_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationLaws_centralMovedReadings : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G), (∀ i σ, w i σ ∈ Subgroup.center G) → R.LUnif → (moveR R w).LUnif := by
  first | exact @GlobalTheory.Unframe.lUnif_moveR | exact GlobalTheory.Unframe.lUnif_moveR | (intros; apply GlobalTheory.Unframe.lUnif_moveR <;> assumption)
end

