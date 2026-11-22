import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0071
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0030
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0034
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0032
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0027
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEtaleNbhdPrimitiveRootOfIsUnitNatCast
section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

private theorem evalRoot {A : Type} [CommRing A] (q : ℕ) :
    Polynomial.eval (AdjoinRoot.root (Polynomial.cyclotomic q A))
      (Polynomial.cyclotomic q (AdjoinRoot (Polynomial.cyclotomic q A))) = 0 := by
  rw [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
    Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

private theorem unitDeriv {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    IsUnit (AdjoinRoot.mk (Polynomial.cyclotomic q A)
      (Polynomial.derivative (Polynomial.cyclotomic q A))) := by
  rcases subsingleton_or_nontrivial (AdjoinRoot (Polynomial.cyclotomic q A)) with h | h
  · exact isUnit_of_subsingleton _
  · have hq' : IsUnit ((q : ℕ) : AdjoinRoot (Polynomial.cyclotomic q A)) := by
      simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))
    have := LateralTheory.E.LeafClosedSH0PfPrim.derivUnit q _ hq' (evalRoot q)
    rwa [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
      Polynomial.derivative_map, Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq] at this

private theorem injOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Injective (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at ha
  refine (Polynomial.cyclotomic.monic q A).not_dvd_of_degree_lt
    (Polynomial.C_ne_zero.2 h0) ?_ ha
  rw [Polynomial.degree_cyclotomic, Polynomial.degree_C h0]
  exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)

private theorem surjOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))) := by
  intro p
  have := (Polynomial.cyclotomic.monic q A).finite_adjoinRoot
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := AdjoinRoot (Polynomial.cyclotomic q A)) p.asIdeal ⊥ (by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (injOf q)]
      exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩

private noncomputable def rootPrim {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    Prim q (AdjoinRoot (Polynomial.cyclotomic q A)) :=
  ⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))), by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact evalRoot q⟩

theorem UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}), IsUnit ((q : ℕ) : Γ(X, ⊤)) → ∀ x : X, ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V) (_ : Prim q Γ(V, ⊤)), f y = x := by
  intro q _ X hq x
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  obtain ⟨p, hp⟩ : x ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hxW
  have hnt : Nontrivial Γ(X, W) := by
    rcases subsingleton_or_nontrivial Γ(X, W) with h | h
    · exact absurd (Subsingleton.elim _ _) p.2.ne_top
    · exact h
  have hqW : IsUnit ((q : ℕ) : Γ(X, W)) := by
    simpa using hq.map (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  have het : Algebra.Etale Γ(X, W) (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    GlobalTheory.etale_adjoinRoot_of_isUnit_derivative (Polynomial.cyclotomic.monic q _) (unitDeriv q hqW)
  let φ : CommRingCat.of Γ(X, W) ⟶ CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).2 het)
  obtain ⟨y0, hy0⟩ := surjOf (A := Γ(X, W)) q p
  let y : Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))) := y0
  have hy : Spec.map φ y = p := hy0
  refine ⟨Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))),
    Spec.map φ ≫ hW.fromSpec, inferInstance, y,
    Prim.map (Scheme.ΓSpecIso _).inv.hom (rootPrim q hqW), ?_⟩
  rw [Scheme.Hom.comp_apply, hy, hp]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPrimitiveFreeOfAcyLocallyExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem sec_comp {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem sec_zero {F G : Shv ℤ} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private theorem UpperTheory.sec_map_res_comm {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) =
    (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem UpperTheory.injective_sec_map_of_mono {F G : Shv ℤ} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

private theorem UpperTheory.acy_of_isZero (Q : Scheme.{0} → Prop) (G : Shv ℤ) (hG : IsZero G) :
    Acy Q G := by
  intro P hP n _
  have hid : (𝟙 G : G ⟶ G) = 0 := hG.eq_of_src _ _
  have hsub : ∀ {U : Scheme.{0}} (x : Sec G U), x = 0 := fun {U} x => by
    calc x = Sec.map (𝟙 G) x := rfl
      _ = 0 := by rw [hid, sec_zero]
  exact UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q G (fun U _ => ⟨fun x y => by rw [hsub x, hsub y]⟩) P hP n

theorem UpperTheory.exists_primitive_free_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → (∀ s, Acy Q (C.X s)) → (∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ P : PSh, Supp Q P → ∀ (j : ℤ) (f : (free ℤ).obj P ⟶ C.X j), f ≫ C.d j (j + 1) = 0 → ∃ g : (free ℤ).obj P ⟶ C.X (j - 1), g ≫ C.d (j - 1) j = f := by
  intro C a _ Q hQ hacy hexact P hP j f hf
  have step : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) →
      Acy Q (kernel (C.d (i + 1) (i + 1 + 1))) ∧ ∀ P : PSh, Supp Q P →
        ∀ f : (free ℤ).obj P ⟶ kernel (C.d (i + 1) (i + 1 + 1)),
          ∃ h, h ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
            (C.d_comp_d _ _ _) = f := by
    intro i hi
    have w : kernel.ι (C.d i (i + 1)) ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
        (C.d_comp_d _ _ _) = 0 := by
      rw [← cancel_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))), Category.assoc, kernel.lift_ι,
        kernel.condition, zero_comp]
    have hex : (ShortComplex.mk (kernel.ι (C.d i (i + 1)))
        (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _)) w).Exact := by
      apply ShortComplex.exact_of_f_is_kernel
      refine KernelFork.IsLimit.ofι _ _
        (fun g' hg' => kernel.lift (C.d i (i + 1)) g' (by
          rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
            ← Category.assoc, hg', zero_comp]))
        (fun g' hg' => kernel.lift_ι _ _ _)
        (fun g' hg' m hm => by
          rw [← cancel_mono (kernel.ι (C.d i (i + 1))), kernel.lift_ι]
          exact hm)
    have hloc : ∀ U : Scheme.{0}, Q U → ∀ b : Sec (kernel (C.d (i + 1) (i + 1 + 1))) U,
        Loc U fun V g => ∃ c, Sec.map (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
          (C.d_comp_d _ _ _)) c = Sec.res g b := by
      intro U hU b
      have hb : Sec.map (C.d (i + 1) (i + 1 + 1))
          (Sec.map (kernel.ι (C.d (i + 1) (i + 1 + 1))) b) = 0 := by
        rw [← sec_comp, kernel.condition, sec_zero]
      have h1 := hexact U hU (i + 1) _ hb
      rw [show i + 1 - 1 = i by omega] at h1
      obtain ⟨S, hS, hSp⟩ := h1
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨c, hc⟩ := hSp V g hg
      refine ⟨c, UpperTheory.injective_sec_map_of_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))) V ?_⟩
      show Sec.map _ (Sec.map _ c) = Sec.map _ (Sec.res g b)
      rw [← sec_comp, kernel.lift_ι, hc, UpperTheory.sec_map_res_comm]
    exact UpperTheory.acy_and_lift_of_locally_surjective_exact Q @hQ _ _ _ _ _ w inferInstance hex hloc hi (hacy i)
  have hAcy : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) := by
    intro i
    rcases lt_or_ge i a with hi | hi
    · exact UpperTheory.acy_of_isZero Q _ (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a i hi))
    · have hi' : a - 1 ≤ i := by omega
      induction i, hi' using Int.le_induction with
      | base =>
        exact UpperTheory.acy_of_isZero Q _
          (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a (a - 1) (by omega)))
      | succ n hn ih =>
        rcases lt_or_ge n a with hn' | hn'
        · exact (step n (UpperTheory.acy_of_isZero Q _
            (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a n hn')))).1
        · exact (step n (ih hn')).1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show i + 1 - 1 = i by omega]
  obtain ⟨h, hh⟩ := (step i (hAcy i)).2 P hP (kernel.lift _ f hf)
  refine ⟨h, ?_⟩
  rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
    ← Category.assoc, hh, kernel.lift_ι]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFiniteFromNormalizationOfPerfectField
section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

theorem UpperTheory.isFinite_fromNormalization_of_perfectField :
    ∀ (k : Type) [Field k] [PerfectField k] {D T : Scheme.{0}} (t : T ⟶ Sp k) [LocallyOfFiniteType t] (f : D ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] [IsIntegral D], IsFinite f.fromNormalization := by
  intro k _ _ D T t _ f _ _ _ _
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(T, U) (integralClosure Γ(T, U) Γ(D, f ⁻¹ᵁ U)) := by
    rcases (f ⁻¹ᵁ U).1.eq_empty_or_nonempty with hE | hN
    · have hb : f ⁻¹ᵁ U = ⊥ := SetLike.ext' hE
      haveI : Subsingleton Γ(D, f ⁻¹ᵁ U) :=
        CommRingCat.subsingleton_of_isTerminal (D.sheaf.isTerminalOfEqEmpty hb)
      infer_instance
    · obtain ⟨x, hx⟩ := hN
      obtain ⟨V, hV, hxV, hVle⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp D.isBasis_affineOpens) hx
      haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
      haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
      have hkt : (t.appLE ⊤ U (by simp)).hom.FiniteType :=
        LocallyOfFiniteType.finiteType_of_affine_subset t (isAffineOpen_top _) hU (by simp)
      let kA : k →+* Γ(T, U) :=
        (t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      have hkA : kA.FiniteType :=
        hkt.comp (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
      letI : Algebra k Γ(T, U) := kA.toAlgebra
      haveI : Algebra.FiniteType k Γ(T, U) := hkA
      haveI : IsNoetherianRing Γ(T, U) := Algebra.FiniteType.isNoetherianRing k Γ(T, U)
      have heq : (D.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom =
          (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom := by
        rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
        congr 1
        simp [Scheme.Hom.appLE]
      let φ : Γ(T, U) →+* D.functionField :=
        (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom
      letI : Algebra Γ(T, U) D.functionField := φ.toAlgebra
      have h1 : (D.germToFunctionField V).hom.EssFiniteType := GlobalTheory.essFiniteType_germ hV _ _
      have h2 : (f.appLE U V hVle).hom.EssFiniteType :=
        (LocallyOfFiniteType.finiteType_of_affine_subset f hU hV hVle).essFiniteType
      haveI : Algebra.EssFiniteType Γ(T, U) D.functionField := h2.comp h1
      haveI := UpperTheory.module_finite_integralClosure_of_finiteType_perfect k Γ(T, U) D.functionField
      let ψ : Γ(D, f ⁻¹ᵁ U) →ₐ[Γ(T, U)] D.functionField :=
        { (D.germToFunctionField (f ⁻¹ᵁ U)).hom with
          commutes' := fun a => by
            change (D.germToFunctionField (f ⁻¹ᵁ U)).hom ((f.app U).hom a) = φ a
            exact congrArg (fun g => g a) heq }
      exact GlobalTheory.finite_integralClosure_of_family (ι := Unit) (L := fun _ => D.functionField)
        (fun _ => ψ) (fun b hb => D.germToFunctionField_injective (f ⁻¹ᵁ U)
          (by rw [map_zero]; exact hb ()))
  rw [CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm.surjective
  · exact (RingHom.finite_algebraMap).mpr h
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.KummerClassAddOfUnitSecAdd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem prim_pow (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

private theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom x) h

private theorem sec_res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U)
    (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y :=
  map_add (F.obj.map g.op).hom x y

private theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ)
    (x : Sec F U) : Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul (φ.hom.app (op U)).hom c x

private theorem unitSec_pow_mul {W : Scheme.{0}} (u w : (Γ(W, ⊤))ˣ) (c : ℕ) :
    unitSec (u ^ c * w) = unitSec w + c • unitSec u := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ', mul_assoc, UpperTheory.PicD.unitSec_mul, ih, succ_nsmul]
    abel

private theorem kumT_pow_mul (q : ℕ) [NeZero q] (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (u w : (Γ(W, ⊤))ˣ)
    (hu : (u : Γ(W, ⊤)) = ζ.1) (c : ℕ) :
    kumT q W (u ^ c * w) = kumT q W w + c • resGen 1 ζ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 W ζ (u ^ c * w) (u ^ (c + 1) * w)
      (by rw [pow_succ', mul_assoc, Units.val_mul, hu])
    rw [h, ih, succ_nsmul, add_assoc]

theorem UpperTheory.kummer_class_add_of_unitSec_add :
    ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) → ∀ (v v' : (Γ(V, ⊤))ˣ) (a : Sec (tw q 1) V), unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from a) → kumT q V v' = kumT q V v + Sec.map (resι _ (tw q 1)) a := by
  intro q _ V hq v v' a h
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ V).1 _ _ ?_
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 V a
  refine ⟨S, hS, fun W g hg => ?_⟩
  show Sec.res g (kumT q V v') = Sec.res g (kumT q V v + Sec.map (resι _ (tw q 1)) a)
  have hK := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g
  let b : Sec (UpperTheory.Deg2.T q) V := a
  let bW : Sec (UpperTheory.Deg2.T q) W := Sec.res g a
  have hb : Sec.res g (Sec.map (UpperTheory.Deg2.kap q) b) = Sec.map (UpperTheory.Deg2.kap q) bW :=
    (sec_map_res (UpperTheory.Deg2.kap q) g b).symm
  have h' : unitSec (Units.map g.appTop.hom.toMonoidHom v') = unitSec (Units.map g.appTop.hom.toMonoidHom v) +
      Sec.map (UpperTheory.Deg2.kap q) bW := by
    have h0 : unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) b := h
    have h1 := congrArg (Sec.res g) h0
    rw [sec_res_add, UpperTheory.PicD.unitSec_res, UpperTheory.PicD.unitSec_res, hb] at h1
    exact h1
  rw [sec_res_add, hK v hq, hK v' hq, ← sec_map_res]
  rcases hP W g hg with h0 | ⟨ζ, c, hc⟩
  · have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = 0 := by
      have : bW = 0 := h0
      rw [this]
      exact sec_map_zero _
    rw [h0, sec_map_zero, add_zero]
    rw [h2, add_zero] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h']
  · have hun : IsUnit ζ.1 := isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q)]
      exact prim_pow q ζ⟩
    obtain ⟨u, hu⟩ := hun
    have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = c • unitSec u := by
      have : bW = c • (show Sec (UpperTheory.Deg2.T q) W from twGen 1 ζ) := hc
      rw [this, sec_map_nsmul, (UpperTheory.Deg2.kap_spec q).2.2.1 W ζ u hu]
    rw [h2, ← unitSec_pow_mul] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h', kumT_pow_mul q W ζ u _ hu c, hc, sec_map_nsmul]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.KummerMapAddOfUnitSecAdd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory

private theorem unitSec_mul {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) :
    unitSec (a * b) = unitSec a + unitSec b :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul a)) (ULift.up (Additive.ofMul b))

private theorem unitSec_pow {U : Scheme.{0}} (a : (Γ(U, ⊤))ˣ) (c : ℕ) :
    unitSec (a ^ c) = c • unitSec a := by
  unfold unitSec ofRings.sec
  exact map_nsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))) c
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul a⟩)

private theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  exact (congrArg (fun f => f.hom (ULift.up (Additive.ofMul u))) h).symm

private theorem unitSec_loc {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) (h : unitSec a = unitSec b) :
    Loc U fun _ g => Units.map g.appTop.hom.toMonoidHom a = Units.map g.appTop.hom.toMonoidHom b := by
  have hx := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U
    ((show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul a⟩) -
      (show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul b⟩)) (by
    rw [map_sub]
    exact sub_eq_zero.mpr h)
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ hx ?_
  intro V g hg
  rw [map_sub, sub_eq_zero] at hg
  have h2 := congrArg (fun t => Additive.toMul (ULift.down t)) hg
  exact h2

private theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => f.hom x) (φ.hom.naturality g.op)).symm

private theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := by
  simp only [Sec.res, map_add]

private theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ)
    (a : Sec F U) : Sec.map φ (c • a) = c • Sec.map φ a :=
  map_nsmul (φ.hom.app (op U)).hom c a

private theorem kum_pow (q : ℕ) [NeZero q] {W : Scheme.{0}} (ζ : Prim q Γ(W, ⊤)) (z : (Γ(W, ⊤))ˣ)
    (hz : (z : Γ(W, ⊤)) = ζ.1) (c : ℕ) (v : (Γ(W, ⊤))ˣ) :
    kumT q W (z ^ c * v) = kumT q W v + c • resGen 1 ζ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 W ζ (z ^ c * v) (z ^ (c + 1) * v) (by
      rw [← hz, pow_succ']; simp [mul_assoc])
    rw [h, ih, succ_nsmul, add_assoc]

end UpperTheory

private theorem kumT_eq_of_unitSec_eq (q : ℕ) [NeZero q] {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))
    (a b : (Γ(U, ⊤))ˣ) (h : unitSec a = unitSec b) : kumT q U a = kumT q U b := by
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ U).1
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (UpperTheory.unitSec_loc a b h) ?_
  intro V g hg
  rw [(GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g a hq, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g b hq, hg]

theorem UpperTheory.kummerMap_add_of_unitSec_add :
    ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) → ∀ (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) → ∀ (v v' : (Γ(V, ⊤))ˣ) (s : Sec (tw q 1) V), Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from s) + unitSec v = unitSec v' → kumT q V v' = kumT q V v + Sec.map (resι _ (tw q 1)) s := by
  intro q _ κ hκ V hq v v' s hs
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ V).1
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 V s) ?_
  intro W g hg
  have hqW : IsUnit (q : Γ(W, ⊤)) := by
    have h1 := hq.map g.appTop.hom
    simpa using h1
  have hsW := congrArg (Sec.res g) hs
  rw [UpperTheory.res_add, UpperTheory.unitSec_res, UpperTheory.unitSec_res,
    UpperTheory.res_map κ g (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from s)] at hsW
  rw [(GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g v' hq, UpperTheory.res_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g v hq, UpperTheory.res_map]
  simp only at hsW
  rcases hg with h0 | ⟨ζ, c, hc⟩
  · have e0 : Sec.map κ (Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s) = 0 := by
      have h3 : Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s = 0 := h0
      rw [h3]
      simp only [Sec.map, map_zero]
    rw [e0, zero_add] at hsW
    rw [h0]
    simp only [Sec.map, map_zero, add_zero]
    exact (kumT_eq_of_unitSec_eq q hqW _ _ hsW).symm
  · obtain ⟨u, hu⟩ : ∃ u : (Γ(W, ⊤))ˣ, (u : Γ(W, ⊤)) = ζ.1 :=
      ⟨Units.ofPowEqOne ζ.1 q ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q _).1 ζ) (NeZero.ne q), rfl⟩
    have hk := hκ W ζ u hu
    simp only at hk
    have e1 : Sec.map κ (Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s) =
        c • unitSec u := by
      have h3 : Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s =
          c • (twGen 1 ζ : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) W) := hc
      rw [h3]
      exact (UpperTheory.map_nsmul' κ c (twGen 1 ζ)).trans (by rw [hk])
    rw [e1, ← UpperTheory.unitSec_pow, ← UpperTheory.unitSec_mul] at hsW
    have h2 := kumT_eq_of_unitSec_eq q hqW _ _ hsW
    rw [UpperTheory.kum_pow q ζ u hu c] at h2
    rw [← h2, hc, UpperTheory.map_nsmul']
    rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.PrimitiveRootEqPowLocally
section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.primitive_root_eq_pow_locally :
    ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ξ ζ : Prim q A) (p : Ideal A) [p.IsPrime], ∃ (f : A) (a : (ZMod q)ˣ), f ∉ p ∧ ∀ (B : Type) [CommRing B] (φ : A →+* B), IsUnit (φ f) → φ ξ.1 = (φ ζ.1) ^ (a : ZMod q).val := by
  intro q _ A _ ξ ζ p _
  have hpow : ∀ η : Prim q A, η.1 ^ q = 1 := by
    intro η
    obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h1 := congrArg (Polynomial.aeval η.1) hg
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, η.2.2, zero_mul] at h1
    exact sub_eq_zero.mp h1
  have hq' : IsUnit ((q : ℕ) : A ⧸ p) := by
    simpa using ζ.2.1.map (Ideal.Quotient.mk p)
  haveI : NeZero ((q : ℕ) : A ⧸ p) := ⟨hq'.ne_zero⟩
  have prim : ∀ η : Prim q A, IsPrimitiveRoot (Ideal.Quotient.mk p η.1) q := by
    intro η
    have h0 : Ideal.Quotient.mk p (Polynomial.aeval η.1 (Polynomial.cyclotomic q ℤ)) = 0 := by
      rw [η.2.2, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot,
      Polynomial.eval_map]
    have e : (Ideal.Quotient.mk p).comp (algebraMap ℤ A) = Int.castRingHom (A ⧸ p) :=
      RingHom.ext_int _ _
    rw [e] at h0
    exact h0
  obtain ⟨k, hk, hkξ⟩ := (prim ζ).eq_pow_of_pow_eq_one (prim ξ).pow_eq_one
  have hcop : k.Coprime q := ((prim ζ).pow_iff_coprime (NeZero.pos q) k).1 (hkξ ▸ prim ξ)
  have hcq : (ζ.1 ^ k) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow ζ, one_pow]
  have hf : (∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) * (ξ.1 - ζ.1 ^ k) = 0 := by
    rw [geom_sum₂_mul, hpow ξ, hcq, sub_self]
  refine ⟨∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i), ZMod.unitOfCoprime k hcop, ?_, ?_⟩
  · intro hmem
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hc : Ideal.Quotient.mk p (ζ.1 ^ k) = Ideal.Quotient.mk p ξ.1 := by
      rw [map_pow, hkξ]
    have hcu : IsUnit (Ideal.Quotient.mk p ξ.1) := by
      refine (Units.ofPowEqOne _ q ?_ (NeZero.ne q)).isUnit
      rw [← map_pow, hpow ξ, map_one]
    rw [map_sum] at hz
    have hsum : ∑ i ∈ Finset.range q, Ideal.Quotient.mk p (ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) =
        ∑ i ∈ Finset.range q, (Ideal.Quotient.mk p ξ.1) ^ (q - 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [map_mul, map_pow, map_pow, hc, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hz
    exact (hq'.mul (hcu.pow _)).ne_zero hz
  · intro B _ φ hφ
    have h1 := congrArg φ hf
    rw [map_mul, map_zero, hφ.mul_right_eq_zero, map_sub, sub_eq_zero] at h1
    rw [h1, map_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
end

