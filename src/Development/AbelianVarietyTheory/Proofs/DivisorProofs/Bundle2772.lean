import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSemiStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairsFixedOverUnramifiedExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UnramCharVals

attribute [local instance] GlobalTheory.TorusExt.gtGroup

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem tor_charVal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (t : GtPtF D F) (k : ℕ), t.b = 1 → (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → ∀ χ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal t χ (closedPoint F) J) : F) ^ k = 1 := by
  intro R _ _ D F _ _ t k h1 hk J hJ χ
  letI := GlobalTheory.TorusExt.gtGroup D F
  have C : IsCub (th D (T := TF (R := R) F) (closedPoint F) J) := isCub_cubV D.cub hJ
  have key : ∀ i : ℕ, GlobalTheory.TorusExt.charVal (i • t) χ (closedPoint F) J = GlobalTheory.TorusExt.charVal t χ (closedPoint F) J ^ i := by
    intro i
    induction i with
    | zero => rw [zero_nsmul, GlobalTheory.TorusExt.zero_val χ hJ, pow_zero]
    | succ i ih =>
      have e := GlobalTheory.TorusExt.add_val (i • t) t χ hJ
      rw [h1, C.face₃, _root_.mul_one, ih] at e
      rw [succ_nsmul, e, pow_succ]
  have e := key k
  rw [hk, GlobalTheory.TorusExt.zero_val χ hJ] at e
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← e, map_one, Units.val_one]

theorem qk_fixed_of_unram : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : (Sp R).Opens), (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, IsUnit (k : V) → ∀ T₁ : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V))) T₁ → (∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, ∃ b : Sp T₁ ⟶ D.toPre.P.A.left, spMap T₁.subtype ≫ b = p.g.b.left) → ∃ T' : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub T₁.subtype T' ∧ ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ z ∈ T', σ z = z) → ∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q := by
  intro R _ _ _ _ D W hW V _ _ _ φ hV _ hcl _ hc k hk T₁ hT₁ hbs
  have hB := D.tau_bimult
  haveI : IsDiscreteValuationRing V := hV.1
  obtain ⟨hdvr, f, hf, hirr⟩ := id hT₁
  haveI := hdvr
  let φ₁ : R →+* T₁ := f.comp φ
  have hφ₁ : ∀ r, (φ₁ r : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r =>
    (hf _).trans (hc r).symm
  have hloc : IsLocalHom f := ⟨fun v hv => by
    by_contra h
    have hv0 : v ≠ 0 := by rintro rfl; rw [map_zero] at hv; exact not_isUnit_zero hv
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hπ
    cases n with
    | zero => exact h (by simp)
    | succ n =>
      rw [map_mul, map_pow, pow_succ] at hv
      exact (hirr π hπ).not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hv))⟩
  have hcl' : spMap φ₁ (closedPoint T₁) ∈ W := by
    have e : spMap φ₁ = spMap f ≫ spMap φ := by
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]; rfl
    have e' : spMap f (closedPoint T₁) = closedPoint V := PrimeSpectrum.ext (Ideal.ext fun r =>
      ⟨fun h e => h (e.map f), fun h e => h (isUnit_of_map_unit f r e)⟩)
    rw [e]
    show (spMap φ) ((spMap f) (closedPoint T₁)) ∈ W
    rw [e']
    exact hcl
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB T₁.subtype Subtype.val_injective J₀ h₀
  have hψ := fun χ => GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing R D.toPre W χ (hW χ) _ T₁ φ₁ hφ₁ hcl' J₀ h₀ J eJ
  have hbw : ∀ (x : TF (R := R) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A) (b : Sp T₁ ⟶ D.toPre.P.A.left),
      spMap T₁.subtype ≫ b = x.left → b ≫ D.toPre.P.A.hom = spMap φ₁ := by
    intro x b hb
    have hd : IsDominant (spMap T₁.subtype) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
    refine ext_of_isDominant (spMap T₁.subtype) ?_
    rw [← Category.assoc, hb, Over.w x]
    show jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R = spMap T₁.subtype ≫ spMap φ₁
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ₁).symm
  choose bb hbb using hbs
  have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := V) (by simpa using hk)
  have fin := GlobalTheory.T.finite_kTorsion_abelianPart_algClosed R D.toPre (AlgebraicClosure (FractionRing V)) k (Nat.one_le_iff_ne_zero.2 hk0)
  obtain ⟨Rep, hRepf, hRep⟩ := GlobalTheory.T.quotientPoints_finite_representatives R D.toPre hB (AlgebraicClosure (FractionRing V)) k hk0 fin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.toPre.X)
  have hS : AddSubgroup.closure (s : Set D.toPre.X) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl
  choose uu huu using fun (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k) χ =>
    GlobalTheory.T.quotientPoint_characterValue_pow_isUnit R D.toPre hB _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ hψ k p (bb p) (hbb p) (hbw _ _ (hbb p)) χ
  let U : Set T₁ˣ := insert 1 ((fun pc : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k × D.toPre.X => uu pc.1 pc.2) '' (Rep ×ˢ (s : Set D.toPre.X)))
  have hU : U.Finite := ((hRepf.prod s.finite_toSet).image _).insert 1
  have hkT : IsUnit (k : T₁) := by simpa using hk.map f
  obtain ⟨T', hT', hroot⟩ := GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots _ T₁ k hkT U hU
  refine ⟨T', hT', fun σ hσT' p q hq => ?_⟩
  have hσT : ∀ t ∈ T₁, σ t = t := fun t ht => hσT' t (hT'.le ht)
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      show σ (algebraMap (FractionRing R) _ (algebraMap R _ r)) = algebraMap (FractionRing R) _ (algebraMap R _ r)
      rw [← hφ₁]; exact hσT _ (φ₁ r).2)
  have hsub : spMap σ.toRingHom ≫ spMap T₁.subtype = spMap T₁.subtype := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact hσT t t.2
  have hfix : ∀ p' ∈ Rep, GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p'.g = p'.g := by
    intro p' hp'
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ p'.g ?_ J hJ ?_
    · rw [← hbb p', ← Category.assoc, hsub]
    · exact GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local R D.toPre _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ σ.toRingHom hσT p'.g (bb p') (hbb p') (hbw _ _ (hbb p')) _ hS
        (fun χ hχ => hσT' _ (hroot _ ⟨uu p' χ, Set.mem_insert_of_mem _ ⟨(p', χ), ⟨hp', hχ⟩, rfl⟩, huu p' χ⟩))
  have hfixt : ∀ t : GtPtF D.toPre (AlgebraicClosure (FractionRing V)), t.b = 1 → k • t = 0 →
      GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ t = t := by
    intro t h1 hkt
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ t ?_ J hJ (fun χ => hσT' _ (hroot _ ⟨1, Set.mem_insert _ _, ?_⟩))
    · rw [h1]
      exact congrArg (fun q => q.left) (MonObj.comp_one (GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ) :
        GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ ≫ (1 : TF (R := R) _ ⟶ D.toPre.P.A) = 1)
    · rw [tor_charVal_pow R D.toPre _ t k h1 hkt J hJ χ]; simp
  obtain ⟨p', hp', z, t, h1, hkt, hpg⟩ := hRep p
  have hg : GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p.g = p.g := by
    rw [hpg, map_add, map_add, hfix p' hp', GlobalTheory.TorusExt.gtExt_iota, hfixt t h1 hkt]
  have hq' := (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hσ p q).1 hq
  refine (GlobalTheory.TorusExt.equiv_iff hB p q).2 ⟨0, ?_, ?_⟩
  · rw [hq', smul_zero, add_zero]; rfl
  · rw [hq', map_zero, add_zero]; exact hg

end GlobalTheory.UnramCharVals
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassMulEqAdd
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

open CartesianMonoidalCategory MonObj
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_comp_stalk {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) {W : Scheme.{0}} (f : W ⟶ (torsion G n).left) (q : W) (c : M)
    (h : ValAt G n ℓ w (f q) c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (z : Sp Ω ⟶ V)
    (hz : y ≫ W.fromSpecStalk q ≫ f ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ W.fromSpecStalk q ≫ f ≫ (torsion.ι G n).left = z ≫ w c := by
  have e := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
  have h1 := h Ω (y ≫ Spec.map (f.stalkMap q)) z (by rw [Category.assoc, reassoc_of% e]; exact hz)
  rwa [Category.assoc, reassoc_of% e] at h1

theorem comp_torsion_ι_mulN {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ torsion G n) :
    (a ≫ torsion.ι G n) ≫ mulN G n = 1 := by
  have e : torsion.ι G n ≫ mulN G n = toUnit (torsion G n) ≫ (η : 𝟙_ (Over X') ⟶ G) :=
    (pullback.condition (f := mulN G n) (g := (η : 𝟙_ (Over X') ⟶ G))).trans
      (congrArg (· ≫ (η : 𝟙_ (Over X') ⟶ G)) (toUnit_unique _ _))
  rw [Category.assoc, e, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem valAt_mul : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (hadd : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a b : M) (A B C : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w b → C.left = x ≫ w (a + b) → C = A * B)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hRT : RT ≫ (torsion.ι G n).left = (P * Q).left) (x : Sp K)
    (cP cQ cR : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ)
    (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = cP + cQ := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ hun hadd K _ _ t P Q PT QT RT hPT hQT hRT x cP cQ cR hcP hcQ hcR
  haveI : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  let h : pullback (torsion G n).hom (torsion G n).hom ⟶ X' :=
    pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  haveI : Etale h := inferInstance
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  haveI : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x)) :=
    isDomain_stalk_of_etale h (pq x)
  obtain ⟨Ω, _, _, y, hy, -⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x))
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat h (pq x) ℓ Ω y hy
  let WO : Over X' := Over.mk h
  let A' : WO ⟶ torsion G n := Over.homMk (pullback.fst (torsion G n).hom (torsion G n).hom) rfl
  let B' : WO ⟶ torsion G n :=
    Over.homMk (pullback.snd (torsion G n).hom (torsion G n).hom) pullback.condition.symm
  let A : WO ⟶ G := A' ≫ torsion.ι G n
  let B : WO ⟶ G := B' ≫ torsion.ι G n
  have hs : (A * B) ≫ mulN G n = 1 := by
    letI : CommGroup (WO ⟶ G) := Hom.commGroup
    rw [GlobalTheory.GrpTangent.comp_mulN, mul_pow, ← GlobalTheory.GrpTangent.comp_mulN, ← GlobalTheory.GrpTangent.comp_mulN,
      comp_torsion_ι_mulN, comp_torsion_ι_mulN, _root_.one_mul]
  obtain ⟨sT, hsT⟩ := exists_lift_torsion n (A * B) hs
  let g : Over.mk t ⟶ WO := Over.homMk pq (by
    show pq ≫ pullback.fst _ _ ≫ _ = t
    rw [pullback.lift_fst_assoc, hPt])
  have hgA : g ≫ A = P := by
    ext1
    simp only [A, A', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_fst_assoc, hPT]
  have hgB : g ≫ B = Q := by
    ext1
    simp only [B, B', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_snd_assoc, hQT]
  have hRT' : pq ≫ sT.left = RT := by
    haveI := mono_torsion_ι G n
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, ← Over.comp_left, hsT, hRT, ← hgA, ← hgB,
      ← MonObj.comp_mul]
    rfl
  have e1 : (pullback.fst (torsion G n).hom (torsion G n).hom) (pq x) = PT x := by
    show (pq ≫ pullback.fst _ _) x = _
    rw [pullback.lift_fst]
  have e2 : (pullback.snd (torsion G n).hom (torsion G n).hom) (pq x) = QT x := by
    show (pq ≫ pullback.snd _ _) x = _
    rw [pullback.lift_snd]
  have e3 : sT.left (pq x) = RT x := by
    show (pq ≫ sT.left) x = _
    rw [hRT']
  rw [← e1] at hcP
  rw [← e2] at hcQ
  rw [← e3] at hcR
  have hP' := valAt_comp_stalk G n ℓ w _ (pq x) cP hcP Ω y z hz
  have hQ' := valAt_comp_stalk G n ℓ w _ (pq x) cQ hcQ Ω y z (by rw [← pullback.condition]; exact hz)
  have hR' := valAt_comp_stalk G n ℓ w sT.left (pq x) cR hcR Ω y z (by rw [Over.w sT]; exact hz)
  let k : Over.mk (z ≫ ℓ) ⟶ WO :=
    Over.homMk (y ≫ (pullback (torsion G n).hom (torsion G n).hom).fromSpecStalk (pq x))
      (by simpa [WO] using hz)
  have hC := hadd Ω z cP cQ (k ≫ A) (k ≫ B) (Over.homMk (z ≫ w (cP + cQ)) (by simp [hw]))
    (by simpa [k, A, A'] using hP') (by simpa [k, B, B'] using hQ') rfl
  rw [← MonObj.comp_mul, ← hsT] at hC
  have hC' := congrArg (fun u => u.left) hC
  simp only [Over.homMk_left, Over.comp_left, k] at hC'
  refine hun Ω z cR (cP + cQ) ?_
  rw [← hR']
  simp only [Category.assoc] at hC'
  exact hC'.symm

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointExtendsOverNormalDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Tors

theorem torsion_extend : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → ∀ x : TF (R := R) (FractionRing R) ⟶ P.A, x ^ N = 1 → ∃ b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A, b ^ N = 1 ∧ x = toUnit _ ≫ b := by
  intro hL R _ _ hR hIC P N hN x hx
  have hfin : IsFinite (mulA P.A N).left := (hL.mulN _ P N hN).1
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp [jFK]
  have hTF : (TF (R := R) (FractionRing R)).hom = jK R := by
    simp [TF, hj]
  have e1 : x ≫ mulA P.A N = toUnit _ ≫ η[P.A] := by
    rw [mulA, MonObj.comp_pow, Category.comp_id, hx]; rfl
  have h : x.left ≫ (mulA P.A N).left = jK R ≫ η[P.A].left := by
    have := congrArg CommaMorphism.left e1
    simp only [Over.comp_left] at this
    rw [this]
    congr 1
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.FiniteLift.exists_lift (mulA P.A N).left η[P.A].left x.left h
  have hl3 : l ≫ P.A.hom = 𝟙 _ := by
    rw [← Over.w (mulA P.A N), ← Category.assoc, hl1, Over.w η[P.A]]
    simp
  let b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A := Over.homMk l (by simpa using hl3)
  refine ⟨b, ?_, ?_⟩
  · have e2 : b ^ N = b ≫ mulA P.A N := by rw [mulA, MonObj.comp_pow, Category.comp_id]
    rw [e2]
    ext1
    simp only [Over.comp_left, b, Over.homMk_left, hl1]
    show _ = (toUnit _ ≫ η[P.A]).left
    rw [toUnit_unit, Category.id_comp]
  · ext1
    simp only [Over.comp_left, b, Over.homMk_left]
    have w := Over.w (toUnit (TF (R := R) (FractionRing R)))
    have w' : (toUnit (TF (R := R) (FractionRing R))).left = jK R := by
      rw [← hTF, ← w]
      first | rfl | simp | (erw [Category.comp_id])
    rw [w', hl2]

end GlobalTheory.Poinc.Tors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj
open GlobalTheory.MBLit GlobalTheory.MBModel

noncomputable section

namespace GlobalTheory.TorsRational

open Polynomial

theorem exists_ext_factor (K R : Type) [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (φ : R →+* Ω), φ.comp (algebraMap K R) = σ.comp (algebraMap K K'') →
        ∃ φ'' : R →+* K'', σ.comp φ'' = φ := by
  classical
  let b := Module.finBasis K R
  let f : K[X] := ∏ i, minpoly K (b i)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  have hroot : ∀ r ∈ Set.range b, aeval r f = 0 := by
    rintro _ ⟨i, rfl⟩
    simp only [f, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K _)
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K'' Ω _ _ _ _ _ σ φ hφ
  have hs : (f.map (algebraMap K K'')).Splits := by
    rw [IsScalarTower.algebraMap_eq K f.SplittingField K'', ← Polynomial.map_map]
    exact (SplittingField.splits f).map _
  have hmem : ∀ r, φ r ∈ σ.range := by
    intro r
    have hr : r ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      refine hs.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) ?_
      rw [Polynomial.map_map, ← hφ, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, hroot x hx, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ⟨algebraMap K K'' c, ?_⟩ hx
      rw [← RingHom.comp_apply, ← hφ, RingHom.comp_apply]
  let e := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => σ.injective (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict σ.range hmem), ?_⟩
  ext r
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict σ.range hmem r))

theorem exists_ext_points (K : Type) [Field K] (T : Over (Sp K)) (hT : IsFinite T.hom) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (t : Sp Ω ⟶ T.left), t ≫ T.hom = spMap (σ.comp (algebraMap K K'')) →
        ∃ w : Sp K'' ⟶ T.left, spMap σ ≫ w = t := by
  haveI : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  letI : Algebra K Γ(T.left, ⊤) := ρ.hom.toAlgebra
  haveI : Module.Finite K Γ(T.left, ⊤) := by
    have : IsFinite (Spec.map ρ) := by rw [hρ]; infer_instance
    exact (IsFinite.SpecMap_iff ρ).1 this
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_factor K Γ(T.left, ⊤)
  refine ⟨K', _, _, hfin, fun K'' Ω _ _ _ _ _ σ t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ T.left.isoSpec.hom)
  have h1 : φ.hom.comp (algebraMap K Γ(T.left, ⊤)) = σ.comp (algebraMap K K'') := by
    have : Spec.map (ρ ≫ φ) = Spec.map (CommRingCat.ofHom (σ.comp (algebraMap K K''))) := by
      rw [Spec.map_comp, hφ, hρ, Category.assoc, Iso.hom_inv_id_assoc, ht]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨φ'', hφ''⟩ := H K'' Ω σ φ.hom h1
  refine ⟨Spec.map (CommRingCat.ofHom φ'') ≫ T.left.isoSpec.inv, ?_⟩
  have e : CommRingCat.ofHom φ'' ≫ CommRingCat.ofHom σ = φ := by
    ext r
    exact congrArg (fun g => g r) hφ''
  rw [← Category.assoc, spMap, ← Spec.map_comp, e, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TorsRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullTot1_bijective | exact GlobalTheory.liftSemi_pullTot1_bijective | (intros; apply GlobalTheory.liftSemi_pullTot1_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageExtensionExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_stage_extension_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  first | exact @GlobalTheory.SqStepK.PiLocalization₂.stage_first | exact GlobalTheory.SqStepK.PiLocalization₂.stage_first | (intros; apply GlobalTheory.SqStepK.PiLocalization₂.stage_first <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_translate_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (G : Over (Sp R)) [GrpObj G] (V : G.left.Opens), IsAffineOpen V → ∀ (a : Over.mk (spMap ρ) ⟶ G), ∃ W : (pullback G.hom (spMap ρ)).Opens, IsAffineOpen W ∧ ∀ (Ω : Type) [Field Ω] (z : Sp Ω ⟶ pullback G.hom (spMap ρ)) (t : Sp Ω ⟶ Sp R) (x a' : Over.mk t ⟶ G), x.left = z ≫ pullback.fst _ _ → a'.left = z ≫ pullback.snd _ _ ≫ a.left → (∀ w, (x * a').left w ∈ V) → ∀ w, z w ∈ W := by
  first | exact @GlobalTheory.Mum.translate_baseChange_affineOpen | exact GlobalTheory.Mum.translate_baseChange_affineOpen | (intros; apply GlobalTheory.Mum.translate_baseChange_affineOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateMulInvIsNonvanishingLocusSquareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_mul_inv_isNonvanishingLocus_square : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.SquareLocus.translate_mul_inv_isLocus | exact GlobalTheory.SquareLocus.translate_mul_inv_isLocus | (intros; apply GlobalTheory.SquareLocus.translate_mul_inv_isLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFractionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  first | exact @GlobalTheory.Mum.transport_extLam | exact GlobalTheory.Mum.transport_extLam | (intros; apply GlobalTheory.Mum.transport_extLam <;> assumption)
end

