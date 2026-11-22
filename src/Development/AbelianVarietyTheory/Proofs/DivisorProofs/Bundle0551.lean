import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0458
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureOfIsArtinianRing
section
open IsLocalRing

namespace GlobalTheory.PurityProd

theorem etale_of_etale_atMaximal {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (h : Algebra.Etale (Localization.AtPrime (maximalIdeal A))
      (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B)) :
    Algebra.Etale A B := by
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x hx => by
      simpa [IsUnit.mem_submonoid_iff] using IsLocalRing.notMem_maximalIdeal.mp hx)
  haveI : Algebra.Etale A (Localization.AtPrime (maximalIdeal A)) := Algebra.Etale.of_equiv e
  haveI : Algebra.Etale A (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B) :=
    Algebra.Etale.comp A (Localization.AtPrime (maximalIdeal A)) _
  let f : TensorProduct A (Localization.AtPrime (maximalIdeal A)) B ≃ₐ[A] B :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid A B)
  exact Algebra.Etale.of_equiv f

theorem isIntegral_of_forall_apply {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

theorem etale_of_etale_pi {R : Type} [CommRing R] [IsNoetherianRing R] {ι : Type} [Finite ι]
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)] [∀ i, Module.Finite R (C i)]
    (h : Algebra.Etale R (∀ i, C i)) (i : ι) : Algebra.Etale R (C i) :=
  ⟨(Algebra.FormallyEtale.pi_iff C).mp inferInstance i,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end GlobalTheory.PurityProd

namespace GlobalTheory.PurityProd

theorem etale_integralClosure_of_isArtinianRing : ∀ (A E : Type) [CommRing A] [IsRegularLocalRing A]
    [CommRing E] [Algebra A E], IsReduced E → IsArtinianRing E → NoZeroSMulDivisors A E →
    Module.Finite A (integralClosure A E) →
    (∀ (q : Ideal A) [q.IsPrime], q.height ≤ 1 → Algebra.Etale (Localization.AtPrime q)
      (TensorProduct A (Localization.AtPrime q) (integralClosure A E))) →
    Algebra.Etale A (integralClosure A E) := by
  intro A E _ _ _ _ hred hart hnz hfin hq
  classical
  by_cases hm : (maximalIdeal A).height ≤ 1
  · exact etale_of_etale_atMaximal (hq (maximalIdeal A) hm)
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A
  haveI := hdom
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  letI (I : MaximalSpectrum E) : Field (E ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  let F : MaximalSpectrum E → Type := fun I => E ⧸ I.asIdeal
  let ψ : E ≃ₐ[A] (∀ I, F I) := (IsArtinianRing.equivPi E).restrictScalars A
  let C : MaximalSpectrum E → Type := fun I => integralClosure A (F I)
  let Ψ : integralClosure A E →ₐ[A] ∀ I, C I := AlgHom.pi fun I =>
    ((Pi.evalAlgHom A F I).comp (ψ.toAlgHom.comp (integralClosure A E).val)).codRestrict
      (integralClosure A (F I)) fun x => x.2.map ((Pi.evalAlgHom A F I).comp ψ.toAlgHom)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply ψ.injective
      funext I
      exact congrArg Subtype.val (congrFun hxy I)
    · intro l
      refine ⟨⟨ψ.symm fun I => (l I).1, ?_⟩, ?_⟩
      · exact (isIntegral_of_forall_apply (fun I => ((l I : F I))) fun I => (l I).2).map
          ψ.symm.toAlgHom
      · funext I
        apply Subtype.ext
        change ψ (ψ.symm fun I => (l I).1) I = (l I).1
        rw [AlgEquiv.apply_symm_apply]
  let Φ : integralClosure A E ≃ₐ[A] ∀ I, C I := AlgEquiv.ofBijective Ψ hΨ
  have hinjF : ∀ I, Function.Injective (algebraMap A (F I)) := by
    intro I
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hne : ψ.symm (Pi.single I 1) ≠ 0 := by
      intro h0
      have := congrArg ψ h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero (by simpa using congrFun this I : (1 : F I) = 0)
    have h0 : a • ψ.symm (Pi.single I 1) = 0 := by
      apply ψ.injective
      rw [map_smul, AlgEquiv.apply_symm_apply, map_zero]
      funext J
      by_cases hJ : J = I
      · subst hJ; simp [Algebra.smul_def, ha]
      · simp [hJ]
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hne
  haveI hfaith : ∀ I, FaithfulSMul A (C I) := fun I => by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    apply hinjF I
    exact congrArg Subtype.val hab
  haveI hfC : ∀ I, FaithfulSMul (C I) (F I) := fun I =>
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI hintC : ∀ I, IsIntegrallyClosed (C I) := fun I =>
    IsIntegrallyClosed.of_isIntegrallyClosedIn (C I) (F I)
  haveI hfinC : ∀ I, Module.Finite A (C I) := fun I =>
    Module.Finite.of_surjective ((Pi.evalAlgHom A C I).toLinearMap.comp Φ.toLinearMap) (by
      intro c
      obtain ⟨x, hx⟩ := Φ.surjective (Pi.single I c)
      exact ⟨x, by simp [hx]⟩)
  haveI : ∀ I, Algebra.Etale A (C I) := by
    intro I
    have key := GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing A (C I)
    refine key ?_ ?_ ?_ ?_
    · exact IsRegularLocalRing.spanFinrank_maximalIdeal
    · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast (le_of_lt (not_le.mp hm))
    · intro hf
      apply hm
      rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hf, Ideal.height_bot]
      exact zero_le_one
    · intro p _ hp
      have h1 := hq p (le_of_eq hp)
      let G : TensorProduct A (Localization.AtPrime p) (integralClosure A E) ≃ₐ[Localization.AtPrime p]
          ∀ J, TensorProduct A (Localization.AtPrime p) (C J) :=
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
          (Algebra.TensorProduct.piRight A (Localization.AtPrime p) (Localization.AtPrime p) C)
      haveI : Algebra.Etale (Localization.AtPrime p)
          (∀ J, TensorProduct A (Localization.AtPrime p) (C J)) := Algebra.Etale.of_equiv G
      exact etale_of_etale_pi (fun J => TensorProduct A (Localization.AtPrime p) (C J)) this I
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocycles
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCZero

noncomputable def clHom (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    Cocycle ((chains R).obj E) (res R F) 0 →+ H R E F 0 :=
  AddMonoidHom.mk' (fun c => CohomologyClass.mk c) (fun a b => CohomologyClass.mk_add a b)

theorem cochain_neg_one_eq_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (β : Cochain ((chains R).obj E) (res R F) (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · exact (GlobalTheory.EtC.HCElements.chains_X_isZero R E p hp).eq_of_src _ _
  · exact (GlobalTheory.EtC.HCElements.res_X_isZero R F q (by omega)).eq_of_tgt _ _

theorem clHom_bijective (R : Type) [CommRing R] (F : Shv R) (E : Spc) : Function.Bijective (clHom R F E) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : CohomologyClass.mk (a - b) = 0 := by
      rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 hab
    rw [CohomologyClass.mk_eq_zero_iff] at h0
    obtain ⟨m, hm, β, hβ⟩ := h0
    obtain rfl : m = -1 := by omega
    rw [cochain_neg_one_eq_zero R F E β, δ_zero] at hβ
    rw [← sub_eq_zero]
    exact Cocycle.ext (by simpa using hβ.symm)
  · obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c, rfl⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  intro R _ F
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  let cE : ∀ X : Scheme.{0}, Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 ≃+ H R (sch.obj X) F 0 :=
    fun X => AddEquiv.ofBijective (clHom R F (sch.obj X)) (clHom_bijective R F (sch.obj X))
  let φ : ∀ X : Scheme.{0}, Sec F X →+ Cochain ((chains R).obj (sch.obj X)) (res R F) 0 :=
    fun X => (AddMonoidHom.mk' (fun c : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 => c.1) (fun _ _ => rfl)).comp
      ((cE X).symm.toAddMonoidHom.comp (e X).toAddMonoidHom)
  have hφ : ∀ X s, φ X s = ((cE X).symm (e X s)).1 := fun _ _ => rfl
  refine ⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop), naturality := ?_ }, fun U => ⟨?_, fun z => ⟨?_, ?_⟩⟩⟩
  · intro U V f
    ext x
    change φ V.unop ((F.obj.map f).hom x) = ((HC R F).map (sch.map f.unop).op).f 0 (φ U.unop x)
    set c := (cE U.unop).symm (e U.unop x) with hc
    have key : (cE V.unop) (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) =
        e V.unop ((F.obj.map f).hom x) := by
      have h1 := he f.unop x
      have h2 : pull R (sch.map f.unop) F 0 (cE U.unop c) =
          CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) := rfl
      rw [hc, AddEquiv.apply_symm_apply] at h2
      rw [h2] at h1
      exact h1
    rw [hφ, hφ, ← key, AddEquiv.symm_apply_apply]
    rfl
  · intro a b hab
    change φ U.unop a = φ U.unop b at hab
    rw [hφ, hφ] at hab
    exact (e U.unop).injective ((cE U.unop).symm.injective (Subtype.ext hab))
  · intro hz
    refine ⟨(e U.unop).symm (cE U.unop (Cocycle.mk z (0 + 1) rfl hz)), ?_⟩
    change φ U.unop _ = z
    rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, rfl⟩
    change δ 0 (0 + 1) (φ U.unop x) = 0
    rw [hφ]
    exact ((cE U.unop).symm (e U.unop x)).2

end GlobalTheory.EtC.HCZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseUnitRigidifiedGenericGenerator
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem rigUnit_exists_ratio {X Y : Scheme.{0}} (M : LB X) (hM : M.IsLB) (f : Y ⟶ X)
    (t t' : LB.Gen (M.pull f)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → M.ι), r z ∈ (M.pull f).U j →
      gm r z ((M.pull f).U j) (t.s j) = gm r z ⊤ w * gm r z ((M.pull f).U j) (t'.s j) := by
  obtain ⟨w, hw⟩ := glue_unit (X := Y) ⊤ (fun j : PUnit → M.ι => (M.pull f).U j) (fun _ => le_top)
    (fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hM (f y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩)
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      have h1 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      have h2 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht' (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 ((map_inv _ _).trans (congrArg (·⁻¹) h2)))).trans
        (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_inv _ _))).symm)
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rfl)
  refine ⟨w, fun Z r z j hj => ?_⟩
  have e := (gm_res r z (le_top : (M.pull f).U j ≤ ⊤) hj w).symm.trans (congrArg (gm r z _) (hw j))
  rw [e, map_mul, map_inv, inv_mul_cancel_right]

theorem rigUnit_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  intro R K _ _ _ _ _ X e he eA heA M rig c hM hrig hcorr a u hu H
  obtain ⟨w, hw⟩ := rigUnit_exists_ratio M hM e (LB.genPull M u e) rig (LB.isGen_genPull M u hu e) hrig
  haveI : Epi (CommRingCat.ofHom (algebraMap R K)) := by
    have := IsLocalization.epi (nonZeroDivisors R) K
    exact this
  haveI : Mono (spMap (algebraMap R K)) := by
    exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))
  have hsnd : eA ≫ pullback.snd X.hom (spMap (algebraMap R K)) = 𝟙 _ := by
    rw [← cancel_mono (spMap (algebraMap R K)), Category.assoc, ← pullback.condition, ← Category.assoc, heA,
      Category.assoc, he, Category.comp_id, Category.id_comp]
  let z : Sp K := (⊥ : PrimeSpectrum K)
  choose J hJ using fun χ : Sp K ⟶ X.left => exists_chart hM (χ z)
  have hG : Good M z J := hJ
  have hv := val_corr hG hcorr (𝟙 _)
  rw [val_pull hG, val_pull hG, Category.id_comp, Category.id_comp,
    val_of (L := M) c eA z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => by rw [heA]),
    val_of (L := M) rig _ z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => rfl)] at hv
  have hi := hJ (spMap (algebraMap R K) ≫ e)
  generalize J (spMap (algebraMap R K) ≫ e) = i at hv hi
  have h1 := H i _ eA z (by
    have : (eA ≫ pullback.fst X.hom (spMap (algebraMap R K))) z ∈ M.U i := by rw [heA]; exact hi
    exact this)
  rw [heA, hsnd] at h1
  have hm : spMap (algebraMap R K) z ∈ (M.pull e).U (fun _ => i) := mem_pull.2 hi
  have h2 := hw _ (spMap (algebraMap R K)) z (fun _ => i) hm
  have h3 : gm (spMap (algebraMap R K)) z ((M.pull e).U (fun _ => i)) ((LB.genPull M u e).s (fun _ => i)) =
      gm (spMap (algebraMap R K) ≫ e) z (M.U i) (u.s i) :=
    (gm_res _ z _ hm _).trans (gm_pull _ e z _ hi _)
  have h4 : (gm (spMap (algebraMap R K)) z ⊤ w).val =
      gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
    have h5 := (congrArg Units.val (h2.symm.trans h3)).trans (h1.trans (congrArg (_ * ·) (congrArg Units.val hv)))
    rw [Units.val_mul] at h5
    exact (Units.mul_left_inj _).1 h5
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, ?_⟩
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  apply φ.injective
  rw [gm_val _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at h4
  refine Eq.trans ?_ h4
  change ((Sp K).presheaf.germ ⊤ z trivial).hom _ = ((Sp K).presheaf.germ ⊤ z trivial).hom _
  congr 1
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Iso.hom_inv_id_apply] at n
  exact n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGeneratorDivBaseUnitEqGeneric
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DivConst

theorem gs_const {R K : Type} [CommRing R] [CommRing K] (g : R →+* K) {X Y : Scheme.{0}} {q : X ⟶ Sp R}
    {p : Y ⟶ Sp K} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (y : Y) (b : R) :
    gs φ y ⊤ (q.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) =
      gs p y ⊤ ((Scheme.ΓSpecIso (.of K)).inv.hom (g b)) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp R ↦ φ.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) w
  have h₂ := congrArg (fun φ : CommRingCat.of R ⟶ Γ(Spec (.of K), ⊤) ↦ φ.hom b)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [gs_eq φ y ⊤ trivial, gs_eq p y ⊤ trivial]
  exact congrArg (Y.presheaf.germ ⊤ y trivial).hom (h₁.trans (congrArg p.appTop.hom h₂.symm))

theorem exists_genPull_eq : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  intro R K _ _ _ X Y φ p w M c a b hab u hu H
  let β : Γ(X.left, ⊤)ˣ := Units.map (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toMonoidHom b
  refine ⟨⟨fun i => u.s i * (res le_top β)⁻¹⟩, fun i j => unit_ext fun x hx => ?_, ?_⟩
  · have e := congrArg (gm (𝟙 X.left) x (M.U i ⊓ M.U j)) (hu i j)
    simp only [map_mul, map_inv] at e ⊢
    rw [e, gm_res _ x _ hx (res le_top β), gm_res _ x _ hx (res le_top β), gm_res _ x _ hx.1 β,
      gm_res _ x _ hx.2 β, mul_assoc]
  · obtain ⟨s⟩ := c
    refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
    have hy' : φ y ∈ M.U (j PUnit.unit) := mem_pull.1 hy
    refine (gm_res _ y _ hy _).trans ((gm_pull (𝟙 Y) φ y _ hy' _).trans ?_)
    have e := H (j PUnit.unit) Y (𝟙 Y) y hy'
    have e' : (gm (𝟙 Y ≫ φ) y ⊤ β).val = gs (𝟙 Y ≫ p) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
      rw [← gs_unit _ y ⊤ trivial, ← hab, Category.id_comp, Category.id_comp]
      exact gs_const _ w y b
    rw [← e', ← Units.val_mul] at e
    rw [map_mul, map_inv, gm_res (𝟙 Y ≫ φ) y _ hy' β, Units.ext e, mul_inv_cancel_comm]
    rfl

end GlobalTheory.DivConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBund
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC

theorem inv_fibQ (q N : ℕ) : Inv q (fibQ q N) := fun U ⟨x⟩ =>
  (show (invP q).obj (op U) from Sx.map (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N)) x).down

theorem inv_pullback_disc (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    Inv q (pullback (trivV N (disc.obj F)) (PGL.pr N)) := fun U ⟨x⟩ =>
  hF U ⟨Sx.map (pullback.fst (trivV N (disc.obj F)) (PGL.pr N)) x⟩

section
variable {q : ℕ}

theorem ev_comp_cochain {E : Spc} {I K : Cx (ZMod q)} {n d w : ℤ} (α : Cochain ((chains (ZMod q)).obj E) I n)
    (ψ : Cochain I K d) (h : n + d = w) (p : ℕ) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + w = t)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp ψ h) p t ht U x = Sec.map (ψ.v s t (by omega)) (ev α p s hs U x) := by
  rw [ev_def, ev_def, Cochain.comp_v α ψ h _ s t hs (by omega)]
  rfl

theorem cast_cocycle {E : Spc} {n n' i i' : ℤ} (hn : n' = n) (hi : i' = i)
    (γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i')) n') :
    ∃ γ' : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n,
      (CohomologyClass.mk γ' : Ht q E n i) = Ht.cast hn hi (CohomologyClass.mk γ) ∧
      ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (w : Sx E k V),
        ev γ'.1 k s hs V w = twCast hi (ev γ.1 k s (by omega) V w) := by
  subst hn hi
  exact ⟨γ, rfl, fun _ _ _ _ _ => rfl⟩

theorem sxmap_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map g (Sx.map f x) = Sx.map (f ≫ g) x := rfl

theorem coe_cocycle_sum {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle K L n) :
    ((∑ j ∈ t, c j : Cocycle K L n) : Cochain K L n) = ∑ j ∈ t, (c j : Cochain K L n) :=
  map_sum (AddMonoidHom.mk' (fun c : Cocycle K L n => (c : Cochain K L n)) (fun _ _ => rfl)) c t

theorem cochain_sum_v {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain K L n) (p p' : ℤ)
    (h : p + n = p') : (∑ j ∈ t, c j).v p p' h = ∑ j ∈ t, (c j).v p p' h :=
  map_sum (AddMonoidHom.mk' (fun c : Cochain K L n => c.v p p' h) (fun a b => Cochain.add_v a b p p' h)) c t

theorem Jsec_sum {N : ℕ} {I : Cx (ZMod q)} {n : ℤ} {U : Scheme.{0}} {ι : Type} (t : Finset ι)
    (c : ι → Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) I n) : Jsec (∑ j ∈ t, c j) = ∑ j ∈ t, Jsec (c j) :=
  map_sum ((toSheafify Scheme.etaleTopology.{0} (cotPre (ZMod q) q N I n)).app (op U)).hom c t

theorem ev_cocycle_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (↑(∑ j ∈ t, c j) : Cochain _ _ _) p s h U x = ∑ j ∈ t, ev (c j).1 p s h U x := by
  rw [coe_cocycle_sum]
  exact map_sum (evHom I n p s h U x) _ t

theorem ev_cochain_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (∑ j ∈ t, c j) p s h U x = ∑ j ∈ t, ev (c j) p s h U x :=
  map_sum (evHom I n p s h U x) c t

end

theorem pbf_disc_model : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  intro q _ N i
  have hz : ∀ j : Fin N, ∃ z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q ((j : ℕ) : ℤ)))
      (2 * ((j : ℕ) : ℤ)), CohomologyClass.mk z = cpow q (c1 q (lineQ q N)) (j : ℕ) :=
    fun j => (cpow q (c1 q (lineQ q N)) (j : ℕ)).mk_surjective
  choose z hz using hz
  have hψ := fun j : Fin N => GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing q N (i - (j : ℕ)) (j : ℕ) i (by ring) (j : ℕ) (z j)
  choose ψ hψ using hψ
  refine ⟨Jcx (ZMod q) q N (res (ZMod q) (tw q i)), ψ,
    GlobalTheory.T.projBundleModelCochainComplex_isStrictlyGE _ q N _ (inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)),
    GlobalTheory.T.injective_projBundleModelCochainComplex_X _ q N _ (fun m => inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X m))), ?_⟩
  intro F hF n
  obtain ⟨θ, hθ1, hθ2⟩ := GlobalTheory.T.exists_iso_trivialProjBundle_prod_fibre q N F hF
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre (ZMod q) q N (res (ZMod q) (tw q i)) F n
  let e₁ : Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i ≃+ Ht q (disc.obj F ⨯ fibQ q N) n i :=
    { toFun := pull _ θ.hom _ _
      invFun := pull _ θ.inv _ _
      left_inv := fun x => by rw [← pull_comp, θ.inv_hom_id, pull_id]
      right_inv := fun x => by rw [← pull_comp, θ.hom_inv_id, pull_id]
      map_add' := map_add _ }
  refine ⟨e₀.trans e₁.symm, fun a => ?_⟩
  rw [AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  change e₀ _ = pull _ θ.hom _ _ (pbfMap q (trivV N (disc.obj F)) n i a)
  rw [GlobalTheory.T.pullback_projBundleFormulaMap_of_factor GlobalTheory.T.cup_chern_kummer_pullback_naturality q (trivV N (disc.obj F)) (lineQ q N) θ.hom prod.fst prod.snd (inv_fibQ q N)
    (inv_pullback_disc q N F hF) hθ1 hθ2 n i a]
  have hα := fun j : Fin N => GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos (ZMod q) F (res (ZMod q) (tw q (i - (j : ℕ)))) (n - 2 * ((j : ℕ) : ℤ)) (a j)
  choose α hαa hα0 using hα
  have hγ := fun j : Fin N => GlobalTheory.T.cupProduct_discreteSpace_fibre_eq_pairing q N F (α j) (z j) (hα0 j)
  choose γ hγc hγv using hγ
  have hγ' := fun j : Fin N => cast_cocycle (q := q) (E := disc.obj F ⨯ fibQ q N)
    (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) (show i - ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) = i by ring) (γ j)
  choose γ' hγ'c hγ'v using hγ'
  let mkH : ∀ {K L : Cx (ZMod q)} {m : ℤ}, Cocycle K L m →+ CohomologyClass K L m :=
    fun {K L m} => AddMonoidHom.mk' CohomologyClass.mk CohomologyClass.mk_add
  have hL : (∑ j, cpost _ (ψ j) (n - 2 * ((j : ℕ) : ℤ)) n (by omega) (a j)) =
      CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) := by
    rw [show CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) =
      mkH (∑ j, zcomp (α j) (ψ j) _) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hαa j]
    rfl
  have hR : (∑ j : Fin N, ((cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (a j))
      (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (cpow q (c1 q (lineQ q N)) j))).cast (by ring) (by ring) :
        Ht q _ n i)) = CohomologyClass.mk (∑ j, γ' j) := by
    rw [show CohomologyClass.mk (∑ j, γ' j) = mkH (∑ j, γ' j) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = CohomologyClass.mk (γ' j)
    rw [hγ'c j, hγc j, hαa j, hz j]
  rw [hL, hR]
  apply he₀
  · intro p hp s h
    have key : ∀ j : Fin N, (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1.v
        (-(p : ℤ)) s h = 0 := fun j => by
      rw [show (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1 =
        (α j).1.comp (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) from rfl]
      rw [Cochain.comp_v _ _ _ _ (-(p : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) s rfl (by omega), hα0 j p hp _ rfl, zero_comp]
    rw [coe_cocycle_sum, cochain_sum_v]
    exact Finset.sum_eq_zero fun j _ => key j
  · intro U x
    have hc := fun j : Fin N => hψ j (n - 2 * ((j : ℕ) : ℤ)) n (by ring) U (ev (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x)
    choose c hc1 hc2 using hc
    refine ⟨∑ j, c j, ?_, ?_⟩
    · rw [ev_cocycle_sum, Jsec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc1 j]
      exact ev_comp_cochain (α j).1 (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) 0 _ n (by simp) (by simp) U x
    · intro k s hs V y
      rw [ev_cochain_sum, ev_cocycle_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc2 j, hγ'v j, hγv j]
      have e2 : Sx.map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y :=
        (sxmap_comp (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) prod.snd y).trans
          (by rw [prod.map_snd, Category.comp_id]; rfl)
      have e1 : (Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) : F.obj (op V)) =
          F.map (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U).op x :=
        (sxmap_comp (E := disc.obj (yoneda.obj U) ⨯ fibQ q N) _ _ y).trans (by
          rw [prod.map_fst]
          rfl)
      have e3 : Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U)
          (ev (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x) =
          ev (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k)
            (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) :=
        (ev_res _ _ _ _ _ _).trans (congrArg _ e1.symm)
      rw [e2, e3]

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramifiedStatement
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_trace_one_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | exact GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | (intros; apply GlobalTheory.LieDisc.exists_integral_add_cc_eq_one <;> assumption)
end

