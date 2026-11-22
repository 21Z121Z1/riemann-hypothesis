import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebraStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_finite) | (exact GlobalTheory.EtC.laurent_vanishing_finite) | (intros; apply GlobalTheory.EtC.laurent_vanishing_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.TwistedGenericPoint

theorem loc_point {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ P V j := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨hsurj, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨k, v, hv⟩ := hsurj u
  exact ⟨𝒰.X k, 𝒰.f k, v, hprop k, hv, hP _ _ (h𝒰 _ (𝒰.f k) (Presieve.ofArrows.mk k))⟩

theorem isEmpty_of_subsingleton (X : Scheme.{0}) [Subsingleton Γ(X, ⊤)] : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  exact not_subsingleton Γ(X, ⊤) inferInstance

theorem smul_residue {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n : ℕ) (y : M) :
    n • y = (ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

end GlobalTheory.TwistedGenericPoint

namespace GlobalTheory

open GlobalTheory.TwistedGenericPoint in

theorem twGen_gen : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  intro q i S ζ U s
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : Subsingleton Γ(S, ⊤) := by
      obtain ⟨hu, _⟩ := ζ.2
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hu))
    have hS := isEmpty_of_subsingleton S
    have hU : IsEmpty U := ⟨fun u => hS.elim (s u)⟩
    exact ⟨fun _ u => (hU.elim u), fun _ hne _ => (hU.elim hne.some)⟩
  · haveI : NeZero q := ⟨hq.ne'⟩
    obtain ⟨-, h2, h3, h4, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
    refine ⟨fun x u => ?_, fun c hne hc => ?_⟩
    · obtain ⟨V, j, v, hj, hjv, c, hc⟩ := loc_point (h2 U (ζ.map s.appTop.hom) x) u
      refine ⟨V, j, v, (c : ZMod q), hj, hjv, ?_⟩
      have e : Sec.pull (j ≫ s) (twGen i ζ) = twGen i ((ζ.map s.appTop.hom).map j.appTop.hom) :=
        h4 V S (j ≫ s) ζ
      rw [e]
      exact hc.trans (smul_residue c _)
    · haveI : Nonempty U := hne
      have e : Sec.pull s (twGen i ζ) = twGen i (ζ.map s.appTop.hom) := h4 U S s ζ
      rw [e] at hc
      have h0 : c.val • twGen i (ζ.map s.appTop.hom) = 0 := by
        rw [smul_residue (q := q), ZMod.natCast_zmod_val]
        exact hc
      have hd := h3 U _ c.val h0
      rw [← ZMod.natCast_zmod_val c]
      exact (ZMod.natCast_eq_zero_iff _ _).2 hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallyInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulInj

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose R hR hRQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h V g (hSP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => hR V g hg)
  · rintro W _ ⟨V, k, g, hg, hk, rfl⟩
    exact hRQ V g hg W k hk

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_empty {U : Scheme.{0}} [IsEmpty U] {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology (P := @Etale) U, fun _ _ hg => hg.elim⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem sglι_left {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom (Sec.map (sglι F) x) = x := by
  have h := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  exact (congrArg (fun f : F ⟶ F => (f.hom.app (op U)).hom x) h).trans rfl

theorem nsmul_eq_zero_of_dvd {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {c : ℕ} (h : q ∣ c)
    (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp only [ULift.down_natCast, ULift.zero_down]
    exact (CharP.cast_eq_zero_iff (ZMod q) q c).2 h
  rw [this, zero_smul]

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res (F := F) g 0 = 0 :=
  map_zero _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x :=
  map_nsmul _ _ _

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul _ _ _

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj
variable {R : Type} [CommRing R]

theorem tmap_nsmul {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) M'] [Module (ULift.{1} R) N']
    (f : M →ₗ[ULift.{1} R] M') (g : N →ₗ[ULift.{1} R] N') (c : ℕ) (s : M) (t : N) :
    TensorProduct.map f g (c • (s ⊗ₜ[ULift.{1} R] t)) = c • (f s ⊗ₜ g t) := by
  rw [map_nsmul, TensorProduct.map_tmul]

theorem tens_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (c • (Sec.res g s ⊗ₜ Sec.res g t)) := by
  classical
  unfold Tens.res
  rw [DirectSum.lmap_lof, tmap_nsmul]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) = c • μ.mul U p.1.1 p.1.2 w p.2 s t := by
  classical
  unfold Pair.lift
  rw [DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]

theorem lof_eq_zero {ι : Type*} [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module (ULift.{1} R) (M i)]
    (i : ι) (x : M i) (h : DirectSum.lof (ULift.{1} R) ι M i x = 0) : x = 0 :=
  DirectSum.of_injective (β := M) i (h.trans (map_zero _).symm)

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj

theorem tw_mul_loc_injective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → (∀ (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c) → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  intro q _ i j k hk hyp K τ hτ φ hφ U a ha
  have Tk := GlobalTheory.T.tateTwist_sections_locally_generated q k
  have Ti := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have Tj := GlobalTheory.T.tateTwist_sections_locally_generated q j
  refine loc_bind (Tk.1 U a) ?_
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact loc_top fun W k' => by rw [res_comp, h0, res_zero]
  ·
    have hres : ∀ (W : Scheme.{0}) (h : W ⟶ V), Sec.res (h ≫ g) a = c • Sec.res h (twGen k ζ) := by
      intro W h
      rw [res_comp, hc, res_nsmul]
    set A := Sec.map (sglι (tw q i)) (twGen i ζ) with hA
    set B := Sec.map (sglι (tw q j)) (twGen j ζ) with hB
    have h1 : c • τ.mul V 0 0 0 (add_zero 0) A B = 0 := by
      rw [← hφ V ζ, ← map_nsmul', ← hc, map_res, ha, res_zero]
    classical
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = 0} =>
        Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V) ⟨(0, 0), by simp⟩ (c • (A ⊗ₜ B))
    have hx : τ.lift V 0 x = 0 := (lift_lof τ V 0 ⟨(0, 0), by simp⟩ A B c).trans h1
    refine loc_bind (hτ.2 V 0 x hx) ?_
    intro V' g' hx'

    set ζ' := ζ.map g'.appTop.hom with hζ'
    have h2 : c • (twGen i ζ' ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ') = 0 := by
      have e2 := lof_eq_zero _ _ _ ((tens_res_lof g' 0 ⟨(0, 0), by simp⟩ A B c).symm.trans hx')
      have e3 : c • (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) ⊗ₜ[ULift.{1} (ZMod q)]
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom (Sec.res g' B)) = 0 :=
        (tmap_nsmul _ _ c _ _).symm.trans ((congrArg (TensorProduct.map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom) e2).trans (map_zero _))
      have ei : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) = twGen i ζ' := by
        have h := (map_res (sglι (tw q i)) g' (twGen i ζ)).symm
        rw [Ti.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      have ej : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom
          (Sec.res g' B) = twGen j ζ' := by
        have h := (map_res (sglι (tw q j)) g' (twGen j ζ)).symm
        rw [Tj.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      rw [ei, ej] at e3
      exact e3
    refine loc_bind (hyp V' ζ' c h2) ?_
    intro V'' g'' hq
    rcases isEmpty_or_nonempty V'' with hV | hV
    · exact loc_empty
    · have hqc := hq hV
      exact loc_top fun W h => by
        rw [hres, nsmul_eq_zero_of_dvd hqc]

end GlobalTheory.EtC.TwMulInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallySurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulSurj

variable {R : Type} [CommRing R]

theorem loc_top (U : Scheme.{0}) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : ∀ V g, P V g → P' V g) :
    Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => h' V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : Loc U P') :
    Loc U fun V g => P V g ∧ P' V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hP'⟩ := h'
  exact ⟨S ⊓ S', GrothendieckTopology.intersection_covering _ hS hS', fun V g hg => ⟨hP V g hg.1, hP' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (h' : ∀ V g, P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let Rs : ∀ ⦃V : Scheme.{0}⦄ ⦃g : V ⟶ U⦄, S.arrows g → Sieve V := fun V g hg => (h' V g (hP V g hg)).choose
  refine ⟨Sieve.bind S.arrows Rs, Scheme.etaleTopology.bind_covering hS fun V g hg => (h' V g (hP V g hg)).choose_spec.1, ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hP V g hg)).choose_spec.2 W k hk

theorem map_comp_apply {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_id_apply {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem res_map {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have := congrArg (fun m => m.hom x) (f.hom.naturality g.op)
  simpa using this.symm

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem smap_add {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map f (x + y) = Sec.map f x + Sec.map f y := map_add _ x y

theorem sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

theorem smap_nsmul {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul _ n x

theorem sres_nsmul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem smap_zero {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} : Sec.map f (0 : Sec F U) = 0 := map_zero _

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

theorem eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  rw [← map_id_apply x, hF.eq_of_src (𝟙 F) 0, map_zero_hom]

def Good {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (x : Sec G U) : Prop :=
  Loc U fun V g => ∃ z : Sec F V, Sec.map φ z = Sec.res g x

theorem good_of {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x : Sec G U} (h : ∃ z, Sec.map φ z = x) : Good φ U x := by
  obtain ⟨z, rfl⟩ := h
  exact loc_top U fun V g => ⟨Sec.res g z, (res_map φ g z).symm⟩

theorem good_bind {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec G U) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (h : ∀ V g, P V g → Good φ V (Sec.res g x)) : Good φ U x := by
  refine loc_bind hP fun V g hg => ?_
  obtain ⟨S, hS, hS'⟩ := h V g hg
  exact ⟨S, hS, fun W k hk => by obtain ⟨z, hz⟩ := hS' W k hk; exact ⟨z, by rw [hz, res_comp]⟩⟩

theorem good_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x x' : Sec G U} (h : Good φ U x) (h' : Good φ U x') :
    Good φ U (x + x') :=
  loc_mono (loc_and h h') fun _ g ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ => ⟨z + z', by rw [smap_add, sres_add, hz, hz']⟩

theorem good_zero {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Good φ U 0 := good_of φ ⟨0, smap_zero _⟩

end GlobalTheory.EtC.TwMulSurj

namespace GlobalTheory.EtC

open TwMulSurj in

theorem tw_mul_locSurj : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0,
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) =
      τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  intro q _ i j k hk K τ hτ φ hφ
  have hT := GlobalTheory.T.tateTwist_sections_locally_generated
  have key_gen : ∀ V (a : Sec (tw q i) V) (b : Sec (tw q j) V),
      Good φ V (τ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) a) (Sec.map (sglι _) b)) := by
    intro V a b
    refine good_bind φ _ ((hT q i).1 V a) ?_
    rintro W g (ha | ⟨ζ, c, ha⟩)
    · apply good_of
      refine ⟨0, ?_⟩
      rw [smap_zero, τ.nat, res_map, res_map, ha, smap_zero]
      simp
    · refine good_bind φ _ ((hT q j).2.1 W ζ (Sec.res g b)) ?_
      rintro W' g' ⟨c', hb⟩
      apply good_of
      refine ⟨(c * c') • twGen k (ζ.map g'.appTop.hom), ?_⟩
      rw [smap_nsmul, hφ, τ.nat, τ.nat, res_map, res_map, res_map, res_map, ha, hb, sres_nsmul, (hT q i).2.2.2.1, smap_nsmul, smap_nsmul]
      simp [mul_comm, mul_smul]
  have key : ∀ V (x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0), Good φ V (τ.lift V 0 x) := by
    intro V x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact good_zero φ V
    | of p t =>
      obtain ⟨⟨s, t'⟩, hst⟩ := p
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact good_zero φ V
      | add u u' hu hu' => rw [map_add, map_add]; exact good_add φ hu hu'
      | tmul a b =>
        have hlift : τ.lift V 0 (DirectSum.of _ ⟨(s, t'), hst⟩ (a ⊗ₜ b)) = τ.mul V s t' 0 hst a b := by
          unfold Pair.lift
          erw [DirectSum.toModule_lof]
          rfl
        rw [hlift]
        by_cases hs : s = 0
        · subst hs
          obtain rfl : t' = 0 := by omega
          have ea : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom a) = a := by
            refine (map_comp_apply _ (sglι _) a).symm.trans ?_
            simp [sglι]; rfl
          have eb : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom b) = b := by
            refine (map_comp_apply _ (sglι _) b).symm.trans ?_
            simp [sglι]; rfl
          rw [← ea, ← eb]
          exact key_gen V _ _
        · have h0 : τ.mul V s t' 0 hst a b = 0 := by
            rw [eq_zero_of_isZero (F := (sgl (tw q i)).X s) (HomologicalComplex.isZero_single_obj_X _ _ _ _ hs) a]
            simp
          rw [h0]
          exact good_zero φ V
    | add x x' hx hx' => rw [map_add]; exact good_add φ hx hx'
  intro U y
  exact good_bind φ y (hτ.1 U 0 y) fun V g ⟨x, hx⟩ => hx ▸ key V x

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw

theorem appTop_comp_apply' {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem isUnit_natCast_of_hom {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (hq : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  have := hq.map g.appTop.hom
  rwa [map_natCast] at this

theorem muVal_pow (q : ℕ) [NeZero q] {U : Scheme.{0}} (y : Sec (muS q) U) : muVal q y ^ q = 1 := by
  have hr := (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y)).2
  change (( _ : Γ(U, ⊤)ˣ) : Γ(U, ⊤)) ^ q = 1
  rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]

theorem etaS_lift_pow (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (z : Sec (muS q) V) (a : ℕ)
    (h : muVal q z = ζ.1 ^ a) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) V
      (Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (a : ZMod q))))) = z := by
  refine (etaS_sec q V _).trans ((eta_mk q Γ(V, ⊤) ζ _).trans ?_)
  apply muVal_injective q V
  rw [h]
  change (((Additive.toMul (((a : ZMod q)) • Additive.ofMul (root q ζ)) : rootsOfUnity q Γ(V, ⊤)) :
    Γ(V, ⊤)ˣ) : Γ(V, ⊤)) = _
  rw [smul_eq, toMul_nsmul, toMul_ofMul, root_pow_coe, ZMod.val_natCast]
  exact (pow_eq_pow_mod a (prim_pow q ζ)).symm

end GlobalTheory.EtC.MuTw

namespace GlobalTheory.EtC.MuTw

theorem etaS_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Surjective ((etaS q).hom.app (op U)).hom := by
  intro q _ U hq y
  have hloc : Loc U fun V g => ∃ s : Sec (tw q 1) V, Sec.map (etaS q) s = Sec.res g y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq) ?_
    rintro V g ⟨ζ⟩
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _
      ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ (muVal q (Sec.res g y)) (muVal_pow q _)) ?_
    rintro W k ⟨a, ha⟩
    refine ⟨_, etaS_lift_pow q W (Prim.map k.appTop.hom ζ) (Sec.res (k ≫ g) y) a ?_⟩
    rw [muVal_res, appTop_comp_apply', ← muVal_res, ha]
    rfl
  obtain ⟨S, hS, hSy⟩ := hloc
  choose s hs using hSy
  have hsh := (tw q 1).cond
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsh
  let fam : Presieve.FamilyOfElements ((tw q 1).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows :=
    fun V g hg => s V g hg
  have hfam : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q Z (isUnit_natCast_of_hom (g₁ ≫ f₁) q hq)
    change Sec.map (etaS q) (Sec.res g₁ (s _ f₁ h₁)) = Sec.map (etaS q) (Sec.res g₂ (s _ f₂ h₂))
    rw [etaS_res, etaS_res, hs, hs]
    apply muVal_injective q Z
    simp only [muVal_res]
    rw [← appTop_comp_apply', ← appTop_comp_apply', e]
  obtain ⟨x, hx, -⟩ := hsh S hS fam hfam
  refine ⟨x, ?_⟩
  have hsep := (muS q).cond
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsep
  refine (hsep S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g (Sec.map (etaS q) x) = Sec.res g y
  rw [← etaS_res]
  have h1 : Sec.res g x = s V g hg := hx g hg
  rw [h1, hs]

end GlobalTheory.EtC.MuTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlatStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistSheaf_isLocallyFlat : ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i) := by
  first | (exact @GlobalTheory.EtC.flatS_tw) | (exact GlobalTheory.EtC.flatS_tw) | (intros; apply GlobalTheory.EtC.flatS_tw  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatEtaleSheafPreservesLocalExactnessStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_flat_etaleSheaf_preserves_local_exactness : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  first | (exact @GlobalTheory.EtC.tensor_flat_loc_exact) | (exact GlobalTheory.EtC.tensor_flat_loc_exact) | (intros; apply GlobalTheory.EtC.tensor_flat_loc_exact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmasStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_complex_lift_and_extension_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  first | exact @GlobalTheory.TowerLift.tower_lemmas | exact GlobalTheory.TowerLift.tower_lemmas | (intros; apply GlobalTheory.TowerLift.tower_lemmas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH0BijectiveH1InjectiveUniversesStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_h0_bijective_h1_injective_universes : VertHas.{1,1} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{1,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) := by
  first | exact @GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | exact GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | (intros; apply GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 <;> assumption)
end

