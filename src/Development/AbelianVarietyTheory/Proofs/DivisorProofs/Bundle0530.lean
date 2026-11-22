import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupCharacterEqOneOfTrivialIntegral
import Formalism.SatakeDualWeyl.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGenerator
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedExists

def constCx {R : Type} [CommRing R] (F : Shv R) : Cx R where
  X _ := F
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

theorem ext_map (Q q : ℕ) (hq : q ∣ Q) (F : Shv (ZMod Q)) (G : Shv (ZMod q))
    (f : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hf : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec F U), Sec.res g (f U a) = f V (Sec.res g a)) :
    ∃ α : (extSh (ZMod.castHom hq (ZMod q))).obj F ⟶ G, ∀ (U : Scheme.{0}) (a : Sec F U),
      Sec.map α (extSh.sec (ZMod.castHom hq (ZMod q)) F U a) = f U a := by
  let ρ : SemiMap (constCx F) (constCx G) :=
    { app := fun U _ => f U
      nat := fun g _ a => hf _ _ g a
      comm := fun U s t a => by
        show Sec.map (0 : G ⟶ G) (f U a) = f U (Sec.map (0 : F ⟶ F) a)
        simp [Sec.map]
        exact ((f U).map_zero).symm }
  exact ⟨FactorExt.term _ (FactorExt.intCast_surj Q) ρ 0,
    fun U a => FactorExt.term_sec _ (FactorExt.intCast_surj Q) ρ 0 U a⟩

def semiOfExt {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) : SemiMap I K where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom.comp ((extπ (ZMod.castHom hq (ZMod q)) I).app U s)
  nat g s a := by
    have h := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op))
      ((extπ (ZMod.castHom hq (ZMod q)) I).app _ s a)).symm
    refine h.trans ?_
    exact congrArg (fun x => ((m.f s).hom.app (op _)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).nat g s a)
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a))) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · exact congrArg (fun x => ((m.f t).hom.app (op U)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).comm U s t a)

theorem semiOfExt_app {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (semiOfExt hq m).app U s a = Sec.map (m.f s) (extSh.sec (ZMod.castHom hq (ZMod q)) (I.X s) U a) := rfl

def powPrim {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.EtC.PrimBasic.prim_basic Q A).2.2.2.2.2 q hq ζ
    rw [← h]
    exact ξ.2⟩

theorem powPrim_map {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (ζ : Prim Q A) : (powPrim hq ζ).map φ = powPrim hq (ζ.map φ) :=
  Subtype.ext (map_pow φ _ _)

theorem nsmul_mod_of {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) (n : ℕ) :
    n • x = (n % q) • x := by
  have hq : q • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext _ _ (by simp)
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm q, mul_smul, hq, smul_zero, add_zero]

theorem twRed_sec : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ), ∃ f : ∀ U : Scheme.{0}, Sec (tw Q i) U →+ Sec (tw q i) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec (tw Q i) U), Sec.res g (f U a) = f V (Sec.res g a)) ∧
    ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → f U (twGen i ζ) = twGen i ξ := by
  intro Q q _ _ hq i
  let M : Shv (ZMod Q) := (restr (ZMod.castHom hq (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (powPrim hq ζ) : Sec (tw q i) U)
  have ts := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim Q Γ(U, ⊤)), Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have := ts.2.2.2.1 V U g (powPrim hq ζ)
    rw [powPrim_map] at this
    exact this
  have hcast : ∀ u : (ZMod Q)ˣ, ((ZMod.unitsMap hq u : (ZMod q)ˣ) : ZMod q).val = (u : ZMod Q).val % q := by
    intro u
    show (ZMod.castHom hq (ZMod q) (u : ZMod Q)).val = _
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a h
    have hq1 : (ζ.1 ^ (Q / q)) ^ q = 1 := (GlobalTheory.EtC.PrimBasic.prim_basic q _).1 (powPrim hq ζ)
    have hpw : (powPrim hq ξ).1 = (powPrim hq ζ).1 ^ ((ZMod.unitsMap hq a : (ZMod q)ˣ) : ZMod q).val := by
      rw [hcast]
      show ξ.1 ^ (Q / q) = (ζ.1 ^ (Q / q)) ^ ((a : ZMod Q).val % q)
      rw [h, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.mod_add_div (a : ZMod Q).val q]
      rw [pow_add, pow_mul, hq1, one_pow, mul_one]
    have h5 := ts.2.2.2.2.1 U (powPrim hq ζ) (powPrim hq ξ) (ZMod.unitsMap hq a) hpw
    show (twGen i (powPrim hq ξ) : Sec (tw q i) U) =
      ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • (twGen i (powPrim hq ζ) : Sec (tw q i) U)
    have hm : (((ZMod.unitsMap hq a) ^ i : (ZMod q)ˣ) : ZMod q).val % q = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val % q := by
      rw [show (ZMod.unitsMap hq a) ^ i = ZMod.unitsMap hq (a ^ i) from (map_zpow _ _ _).symm, hcast, Nat.mod_mod]
    rw [h5, nsmul_mod_of (q := q) (twGen i (powPrim hq ζ)), hm, ← nsmul_mod_of (q := q)]
  obtain ⟨β, hβ, -⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).2.2.2.2.2 M e he1 he2
  refine ⟨fun U => ⟨⟨fun a => ((β.hom.app (op U)).hom a : Sec (tw q i) U), (β.hom.app (op U)).hom.map_zero⟩,
    fun a b => (β.hom.app (op U)).hom.map_add a b⟩, ?_, ?_⟩
  · intro V U g a
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (β.hom.naturality g.op)) a).symm
  · intro U ζ ξ h
    have h1 := hβ U ζ
    have h2 : powPrim hq ζ = ξ := Subtype.ext h.symm
    exact h1.trans (congrArg (twGen i) h2)

theorem redMap_exists (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ) :
    ∃ ρ : SemiMap (res _ (tw Q i)) (res _ (tw q i)), ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)),
      ξ.1 = ζ.1 ^ (Q / q) → ρ.app U 0 (resGen i ζ) = resGen i ξ := by
  obtain ⟨f, hf, hfg⟩ := twRed_sec Q q hq i
  obtain ⟨α, hα⟩ := ext_map Q q hq (tw Q i) (tw q i) f hf
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  have hQ := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))
    (extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) (res _ (tw q i))
    (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).1
    ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i))
  refine ⟨semiOfExt hq m, fun U ζ ξ h => ?_⟩
  have hv : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 := by
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        m.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ m.f 0) hs').trans (Category.assoc _ _ _)
  have hw : ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        α ≫ resι _ (tw q i) := by
    rw [HomologicalComplex.comp_f, ← hι]
    change ((HomologicalComplex.single (Shv (ZMod q)) (ComplexShape.up ℤ) 0).map α).f 0 ≫ _ = _
    rw [HomologicalComplex.single_map_f_self]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ?_
    exact Category.assoc _ _ _
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 = α ≫ resι _ (tw q i) := by
    have e : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
        ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 := by rw [hm]
    rw [hv, hw] at e
    exact (cancel_epi _).1 e
  rw [semiOfExt_app]
  change Sec.map (m.f 0) (extSh.sec _ _ U (Sec.map (resι _ (tw Q i)) (twGen i ζ))) = Sec.map (resι _ (tw q i)) (twGen i ξ)
  rw [← extSh.sec_map, ← hfg U ζ ξ h, ← hα]
  have e2 := congrArg (fun k => Sec.map k (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) U (twGen i ζ))) key
  exact e2

theorem red_exists : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  intro Q q _ _ hq i U ζ ξ h
  exact pick_spec (redMap_exists Q q hq i) U ζ ξ h

end GlobalTheory.EtC.RedExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceIntegralOfPreservedLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LatTrace

open Polynomial

theorem aeval_mulVec_of_eigen {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : Type*}
    [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (μ : S) (v : n → S) (hv : Q *ᵥ v = μ • v) (p : R[X]) :
    (aeval Q p) *ᵥ v = (aeval μ p) • v := by
  have hpow : ∀ k : ℕ, (Q ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, hpow,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_mul_assoc, one_mul, smul_assoc]

theorem aeval_restrict_coe {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (L : Submodule ℤ (n → S))
    (hQ : ∀ x ∈ L, (Q.mulVecLin.restrictScalars ℤ) x ∈ L) (p : ℤ[X]) (x : L) :
    ((aeval (LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ) p x : L) : n → S) =
      (aeval Q p) *ᵥ (x : n → S) := by
  set f := LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ
  have hpow : ∀ k : ℕ, (((f ^ k) x : L) : n → S) = (Q ^ k) *ᵥ (x : n → S) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, pow_succ',
        ← Matrix.mulVec_mulVec, ← ih]
      rfl
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq,
      Matrix.add_mulVec]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]

theorem isIntegral_trace_of_isIntegral {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨p, hpm, hp0⟩ := hM
  have hpM : aeval M p = 0 := by rw [aeval_def]; exact hp0
  set M' := M.map φ
  have hpM' : aeval M' p = 0 := by
    have h := Polynomial.aeval_algHom_apply (φ.mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hpM, map_zero] at h
    exact h
  have htr : φ M.trace = M'.trace := by
    simp [Matrix.trace, M', map_sum]
  have hroots : ∀ μ ∈ M'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have h0 : M'.charpoly.eval μ = 0 := (Polynomial.mem_roots'.1 hμ).2
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hev : M' *ᵥ v = μ • v := by
      have h1 : (Matrix.scalar (Fin n) μ - M') *ᵥ v = μ • v - M' *ᵥ v := by
        rw [Matrix.sub_mulVec]
        congr 1
        ext i
        simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [h1, sub_eq_zero] at hv
      exact hv.symm
    have h2 := aeval_mulVec_of_eigen M' μ v hev p
    rw [hpM', Matrix.zero_mulVec] at h2
    have hz : aeval μ p = 0 := by
      by_contra hne
      exact hv0 ((smul_eq_zero.1 h2.symm).resolve_left hne)
    exact ⟨p, hpm, by rw [← aeval_def]; exact hz⟩
  have hsum : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    have := multiset_sum_mem (M'.charpoly.roots)
      (fun x hx => ((mem_integralClosure_iff ℤ (AlgebraicClosure K)).2 (hroots x hx) : x ∈ integralClosure ℤ (AlgebraicClosure K)))
    exact (mem_integralClosure_iff ℤ (AlgebraicClosure K)).1 this
  rw [← htr] at hsum
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hsum

theorem isIntegral_of_preserves_lattice {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hA : ∀ x ∈ Λ, A *ᵥ x ∈ Λ) :
    IsIntegral ℤ A := by
  set Lz := Λ.restrictScalars ℤ
  have : Module.Finite ℤ Lz := Module.Finite.iff_fg.mpr hfg.restrictScalars
  have hAz : ∀ x ∈ Lz, (A.mulVecLin.restrictScalars ℤ) x ∈ Lz := fun x hx => hA x hx
  obtain ⟨p, hpm, hp⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero ℤ
      (LinearMap.restrict (A.mulVecLin.restrictScalars ℤ) hAz)
  have hpA : aeval A p = 0 := by
    have hker : ∀ x ∈ Λ, (aeval A p) *ᵥ x = 0 := by
      intro x hx
      have h := aeval_restrict_coe A Lz hAz p ⟨x, hx⟩
      rw [hp] at h
      rw [← h]; rfl
    have hle : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker (aeval A p).mulVecLin :=
      Submodule.span_le.2 fun x hx => hker x hx
    rw [hsp] at hle
    ext i j
    have h := congrFun (hle (Submodule.mem_top : Pi.single j (1 : E) ∈ ⊤)) i
    simpa [Matrix.mulVec_single] using h
  exact ⟨p, hpm, by rw [← aeval_def]; exact hpA⟩

theorem trace_isIntegral_of_preserves_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, A *ᵥ x ∈ Λ) →
    IsIntegral ℤ A.trace := by
  intro E _ _ r Λ A hfg hsp hA
  exact isIntegral_trace_of_isIntegral A (isIntegral_of_preserves_lattice Λ A hfg hsp hA)

end GlobalTheory.LatTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceProductSkewHermitianReal
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem skew_transpose_mul_add_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    Xᵀ * G + G * X.map (fun x => cc x) = 0 := by
  ext i j
  have h := hX (Pi.single i 1) (Pi.single j 1)
  have c0 : cc (0 : E) = 0 := map_zero _
  have c1 : cc (1 : E) = 1 := map_one _
  have hc : ∀ b : Fin r, cc (if b = j then (1 : E) else 0) = if b = j then 1 else 0 := by
    intro b; split_ifs <;> simp [c0, c1]
  simp [herm, Matrix.mulVec_single, Pi.single_apply, c0, c1, hc, Matrix.mul_apply] at h ⊢
  exact h

theorem conj_eq_of_skew {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    X.map (fun x => cc x) = -(G⁻¹ * Xᵀ * G) := by
  have h := skew_transpose_mul_add_mul_conj G X hX
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have h2 : G * X.map (fun x => cc x) = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right h
  calc X.map (fun x => cc x) = G⁻¹ * (G * X.map (fun x => cc x)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = -(G⁻¹ * Xᵀ * G) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]

theorem trace_mul_skew_mem_maximalRealSubfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X Y : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace ∈ maximalRealSubfield E := by
  intro E _ _ _ r G X Y _ hG hX hY
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hXc := conj_eq_of_skew G X hG hX
  have hYc := conj_eq_of_skew G Y hG hY
  rw [← IsCMField.complexConj_eq_self_iff]
  change cc (X * Y).trace = (X * Y).trace
  have hmap : cc (X * Y).trace = ((X * Y).map (fun x => cc x)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum (IsCMField.complexConj E : E →+* E) _ _
  have hmul : (X * Y).map (fun x => cc x) = X.map (fun x => cc x) * Y.map (fun x => cc x) :=
    Matrix.map_mul (f := ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E))
  rw [hmap, hmul, hXc, hYc, neg_mul_neg]
  have e1 : G⁻¹ * Xᵀ * G * (G⁻¹ * Yᵀ * G) = G⁻¹ * (Xᵀ * Yᵀ * G) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem traceZeroIndex_of_intIndex : IntIndex → TraceZeroIndex := by
  intro hI L _ _ ϖ σ q hU
  have hq := hI L ϖ σ q hU
  obtain ⟨hσσ, hv, hϖ, -, ⟨x, hx, hδ⟩, -, -⟩ := hU
  have hσO : ∀ y ∈ intL L, σ y ∈ intL L := fun y hy => by
    show Valued.v (σ y) ≤ 1
    rw [hv]; exact hy
  have hδ0 : σ x - x ≠ 0 := fun h => by rw [h, map_zero] at hδ; exact zero_ne_one hδ
  have hδ1 : x - σ x ≠ 0 := fun h => hδ0 (by linear_combination -h)
  have hδi : (σ x - x)⁻¹ ∈ intL L := by
    show Valued.v (σ x - x)⁻¹ ≤ 1
    rw [map_inv₀, hδ, inv_one]
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y = -y := fun y => by
    rw [hT, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, ← add_eq_zero_iff_eq_neg]
    rfl
  have hw : ∀ y ∈ intL L, σ y - y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (hσO y hy) hy, by rw [map_sub, hσσ]; ring⟩
  have hu : ∀ y ∈ intL L, σ x * y - x * σ y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (mul_mem (hσO x hx) hy) (mul_mem hx (hσO y hy)), by
      rw [map_sub, map_mul, map_mul, hσσ, hσσ]; ring⟩
  let f : T × T →+ (intL L).toAddSubgroup :=
    { toFun := fun p => ⟨(σ x - x)⁻¹ * (p.1.1 + x * p.2.1),
        (intL L).mul_mem hδi ((intL L).add_mem ((memT _).1 p.1.2).1 ((intL L).mul_mem hx ((memT _).1 p.2.2).1))⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp; ring) }
  have hf : ∀ p, (f p : L) = (σ x - x)⁻¹ * (p.1.1 + x * p.2.1) := fun _ => rfl
  have hsurj : Function.Surjective f := fun y =>
    ⟨(⟨_, hu y.1 y.2⟩, ⟨_, hw y.1 y.2⟩), Subtype.ext (by rw [hf]; field_simp; ring)⟩
  have hc : (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup).comap f =
      ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T).prod ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T) := by
    ext ⟨u, w⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map,
      hf, AddMonoidHom.coe_mulLeft]
    constructor
    · rintro ⟨y, hy, e⟩
      have e1 : (σ x - x) * (ϖ * y) = u.1 + x * w.1 := by rw [e]; field_simp
      have e2 := congrArg σ e1
      rw [map_mul, map_sub, hσσ, map_mul, hϖ, map_add, map_mul, ((memT _).1 u.2).2, ((memT _).1 w.2).2] at e2
      have e3 : ϖ * (σ y - y) = w.1 := mul_left_cancel₀ hδ0 (by linear_combination -e1 - e2)
      exact ⟨⟨_, hu y hy, by linear_combination e1 - x * e3⟩, _, hw y hy, e3⟩
    · rintro ⟨⟨a, ha, e1⟩, b, hb, e2⟩
      refine ⟨_, (f (⟨a, ha⟩, ⟨b, hb⟩)).2, ?_⟩
      rw [hf, ← e1, ← e2]; ring
  have h2 := AddSubgroup.index_comap_of_surjective
    (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup) hsurj
  rw [hc, AddSubgroup.index_prod, ← pow_two] at h2
  exact Nat.pow_left_injective two_ne_zero (h2.trans hq)

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCover
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc

open Classical in

theorem twoCocycle_comma_coboundary_of_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hcov hfil T n d hd z hz hy
  choose y hy using hy
  have hu : ∀ {t t' : C'} {u : T ⟶ G.obj t} (a : t ⟶ t') {x : F.obj T}, IsUnit (mp F u x) →
      IsUnit (mp F (u ≫ G.map a) x) := fun a _ h ↦ isUnit_comp _ h
  have h1 := fun i j : Fin n ↦ GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt F G H hcov hfil T (d i * d j)
    (fun t t' u a ↦ y j t t' u a - y i t t' u a) fun t t' t'' u a b h ↦ by
      rw [map_mul, IsUnit.mul_iff] at h
      rw [map_sub]
      linear_combination hy i t t' t'' u a b h.1 - hy j t t' t'' u a b h.2
  choose β hβ' using h1
  have hβ : ∀ i j t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u (d i)) →
      IsUnit (mp F u (d j)) →
      β i j t' (u ≫ G.map a) - mp F (G.map a) (β i j t u) = y j t t' u a - y i t t' u a :=
    fun i j t t' u a hi hj ↦ hβ' i j t t' u a (by rw [map_mul]; exact hi.mul hj)
  have h2 := fun i j k : Fin n ↦ GlobalTheory.T.sections_invertibleLocus_of_basisFunctor F G H hcov hfil T (d i * d j * d k)
    (fun t u ↦ β j k t u - β i k t u + β i j t u) fun t t' u a h ↦ by
      rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at h
      rw [map_add, map_sub]
      linear_combination hβ j k t t' u a h.1.2 h.2 - hβ i k t t' u a h.1.1 h.2 +
        hβ i j t t' u a h.1.1 h.1.2
  choose x hx' hxs' using h2
  have hx : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (d i)) ∧ IsUnit (mp F u (d j))) ∧
      IsUnit (mp F u (d k))) (x i j k) := fun i j k S S' u ψ h ↦
    hx' i j k S S' u ψ (by
      show IsUnit _
      rw [map_mul, map_mul]; exact (h.1.1.mul h.1.2).mul h.2)
  have hxs : ∀ i j k t (u : T ⟶ G.obj t), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      IsUnit (mp F u (d k)) → x i j k (G.obj t) u = β j k t u - β i k t u + β i j t u :=
    fun i j k t u hi hj hk ↦ hxs' i j k t u (by rw [map_mul, map_mul]; exact (hi.mul hj).mul hk)
  obtain ⟨e, he, he'⟩ := cech2 H hd x hx (fun l i j k S u hl hi hj hk ↦ by
    obtain ⟨m, b, hb, hb'⟩ := hcov S
    refine sep_std H hb _ fun S' ψ ⟨r, hr⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' r S' ψ hr
    have hl' := isUnit_comp v hl
    have hi' := isUnit_comp v hi
    have hj' := isUnit_comp v hj
    have hk' := isUnit_comp v hk
    rw [mp_comp, map_sub (mp F v), map_add (mp F v), map_sub (mp F v),
      ← hx i j k S _ u v ⟨⟨hi, hj⟩, hk⟩, ← hx l j k S _ u v ⟨⟨hl, hj⟩, hk⟩,
      ← hx l i k S _ u v ⟨⟨hl, hi⟩, hk⟩, ← hx l i j S _ u v ⟨⟨hl, hi⟩, hj⟩,
      hxs _ _ _ _ _ hi' hj' hk', hxs _ _ _ _ _ hl' hj' hk', hxs _ _ _ _ _ hl' hi' hk',
      hxs _ _ _ _ _ hl' hi' hj']
    ring_nf
    exact map_zero _)
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ i j t u,
      IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      γ j t u - γ i t u = β i j t u - e i j (G.obj t) u := by
    refine ⟨fun i t u ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      β h.choose i t u - e h.choose i _ u else 0, fun i j t u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j _ u h.choose_spec hi hj + hxs _ i j t u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ i t t' u a,
      IsUnit (mp F u (d i)) →
      α t t' u a = y i t t' u a - (γ i t' (u ≫ G.map a) - mp F (G.map a) (γ i t u)) := by
    refine ⟨fun t t' u a ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      y h.choose t t' u a - (γ h.choose t' (u ≫ G.map a) - mp F (G.map a) (γ h.choose t u)) else 0,
      fun i t t' u a hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F (G.map a)) (hγ i _ t u hi h.choose_spec)
    have k2 := hγ i _ t' (u ≫ G.map a) (hu a hi) (hu a h.choose_spec)
    have k3 := he i _ _ _ u (G.map a) ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ t t' u a hi h.choose_spec
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun t t' t'' u a b ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (hu a hi)]
  simp only [map_sub, mp_comp, Category.assoc, G.map_comp]
  linear_combination hy i t t' t'' u a b hi

end GlobalTheory.CatCoh.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupCharacterEqOneOfTrivialIntegralStatement
section
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_character_eq_one_of_trivial_integral : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → J ∈ GLint (Fin n) (intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle, (∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.UnitaryCharacter.char_eq_one | exact GlobalTheory.UnitaryCharacter.char_eq_one | (intros; apply GlobalTheory.UnitaryCharacter.char_eq_one <;> assumption)
end

