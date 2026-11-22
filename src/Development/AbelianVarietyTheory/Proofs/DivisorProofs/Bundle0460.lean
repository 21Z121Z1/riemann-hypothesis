import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSuppSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppo
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppAcyc

variable {R : Type} [CommRing R]

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

theorem map_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

theorem res_zero' {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

theorem cpush_zero (K I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpush, cpost_mk]
  have : zcomp x (Cocycle.ofHom (0 : I ⟶ J)) (add_zero n) = 0 := Cocycle.ext (by simp [zcomp])
  rw [this]
  exact CohomologyClass.mk_zero _ _ _

theorem delta_comp_ofHom {K I J : Cx R} {n : ℤ} (a : Cochain K I n) (f : I ⟶ J) :
    δ n (n + 1) (a.comp (Cochain.ofHom f) (add_zero n)) = (δ n (n + 1) a).comp (Cochain.ofHom f) (add_zero _) := by
  rw [δ_comp _ _ (add_zero n) (n + 1) 1 (n + 1) rfl rfl (zero_add 1)]
  simp

end GlobalTheory.EtC.SuppAcyc

open GlobalTheory.EtC.SuppAcyc in

theorem GlobalTheory.EtC.subsingleton_of_locExact_supp : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  intro R _ E C _ hC n
  let Z : Scheme.{0} → Prop := fun U => Nonempty (Sx E 0 U)
  have hZ : ∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V := fun V U g ⟨x⟩ => ⟨Sx.res g x⟩
  obtain ⟨D, ι, hinj, hchar⟩ := SuppSub.exists_supp_sub R C Z hZ
  obtain ⟨ltop, lmono, -, -, ltrans, -, -⟩ := GlobalTheory.EtC.loc_calculus
  have hin : ∀ k U (a : Sec (C.X k) U), Z U → ∃ b, Sec.map (ι.f k) b = a := fun k U a hU =>
    (hchar k U a).2 (ltop _ _ fun V g => Or.inl (hZ V U g hU))

  have hD : D.Acyclic := by
    intro k
    rw [HomologicalComplex.exactAt_iff' D (k - 1) k (k + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
    intro U (b : Sec (D.X k) U) hb
    change Sec.map (D.d k (k + 1)) b = 0 at hb
    have hc : Sec.map (C.d k (k + 1)) (Sec.map (ι.f k) b) = 0 := by
      rw [← map_comp, ι.comm, map_comp, hb, map_zero']
    have hloc := (hchar k U (Sec.map (ι.f k) b)).1 ⟨b, rfl⟩
    refine ltrans _ _ (lmono _ _ _ hloc fun V g hg => ?_)
    rcases hg with hV | h0
    · have hc' : Sec.map (C.d k (k + 1)) (Sec.res g (Sec.map (ι.f k) b)) = 0 := by
        have := congrArg (Sec.res g) hc
        rwa [SuppSub.res_map, res_zero'] at this
      refine lmono _ _ _ (hC V hV k _ hc') fun W h => ?_
      rintro ⟨a, ha⟩
      obtain ⟨a', rfl⟩ := hin (k - 1) W a (hZ W V h hV)
      refine ⟨a', hinj k W ?_⟩
      change Sec.map (ι.f k) (Sec.map (D.d (k - 1) k) a') = Sec.map (ι.f k) (Sec.res (h ≫ g) b)
      rw [← map_comp, ← ι.comm, map_comp, ha, SuppSub.res_comp, SuppSub.res_map, SuppSub.res_map]
    · have h0' : Sec.res g b = 0 := hinj k V (by rw [← SuppSub.res_map, h0, map_zero'])
      refine ltop _ _ fun W h => ⟨0, ?_⟩
      change Sec.map (D.d (k - 1) k) 0 = Sec.res (h ≫ g) b
      rw [map_zero', SuppSub.res_comp, h0', res_zero']
  have hnull : Nonempty (Homotopy ι 0) := IsKInjective.nonempty_homotopy_zero ι hD
  have hpush : cpush ((chains R).obj E) ι n = cpush _ (0 : D ⟶ C) n :=
    ((GlobalTheory.EtC.ZcFun.main R).2.2.2.2 ι 0 hnull ((chains R).obj E) n).2
  obtain ⟨-, hnat, hdet, -, -⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := C) (n := n)
  obtain ⟨-, -, -, -, hpost⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := D) (n := n)
  obtain ⟨haddD1, -, hdetD, -, hpost1⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := D) (n := n + 1)
  obtain ⟨haddC1, -, -, -, -⟩ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := C) (n := n + 1)
  have hzero : ∀ c : CohomologyClass ((chains R).obj E) C n, c = 0 := by
    intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective

    have hv : ∀ (p : ℕ) (U : Scheme.{0}), Sx E p U → Z U := fun p U x =>
      ⟨Sx.along x (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk p) 0)⟩
    let v : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (D.X s) U :=
      fun p s h U x => Classical.choose (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvspec : ∀ p s h U x, Sec.map (ι.f s) (v p s h U x) = ev α.1 p s h U x :=
      fun p s h U x => Classical.choose_spec (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (v p s h U x) = v p s h V (x.res g) := by
      intro p s h V U g x
      apply hinj s V
      rw [← SuppSub.res_map, hvspec, hvspec, (hnat α.1 p s h V U g x)]
    obtain ⟨α', hα'⟩ := GlobalTheory.EtC.exists_cochain_ev_eq_of_natural R v hvnat
    have hcomp : α'.comp (Cochain.ofHom ι) (add_zero n) = α.1 := by
      apply hdet
      intro p s h U x
      rw [hpost, hα', hvspec]
    have hcoc : δ n (n + 1) α' = 0 := by
      apply hdetD
      intro p s h U x
      apply hinj s U
      rw [← hpost1, ← delta_comp_ofHom, hcomp, (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2, (haddC1 0 0 p s h U x).2.2.1,
        (haddD1 0 0 p s h U x).2.2.1, map_zero']
    let β : Cocycle ((chains R).obj E) D n := Cocycle.mk α' (n + 1) rfl hcoc
    have hαβ : α = zcomp β (Cocycle.ofHom ι) (add_zero n) := Cocycle.ext hcomp.symm
    rw [hαβ, ← cpost_mk, ← cpush, hpush, cpush_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_sections_locally_generated : ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  first | (exact @GlobalTheory.EtC.twist_sections) | (exact GlobalTheory.EtC.twist_sections) | (intros; apply GlobalTheory.EtC.twist_sections  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in

theorem _root_.GlobalTheory.EtC.flatS_tw : ∀ (q : ℕ) [NeZero q] (i : ℤ),
    _root_.GlobalTheory.EtC.FlatS (_root_.GlobalTheory.EtC.tw q i) := by
  intro q _ i
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q)
    (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i)
  refine ⟨_, toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i), h1, h2,
    fun U hU => ?_⟩
  obtain ⟨x⟩ := hU
  haveI : Nontrivial Γ(U, ⊤) := (U.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  haveI := (_root_.GlobalTheory.TwFree.twist_free q i Γ(U, ⊤)).1
  change Module.Flat (ULift.{1} (ZMod q))
    ((_root_.GlobalTheory.EtC.Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸
      _root_.GlobalTheory.EtC.twRel q i Γ(U, ⊤))
  infer_instance

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatEtaleSheafPreservesLocalExactness
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace TensFlat

variable {R : Type} [CommRing R]

theorem rl_comm {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) P] [Module (ULift.{1} R) Q]
    (f : M →ₗ[ULift.{1} R] P) (g : N →ₗ[ULift.{1} R] Q) (x : TensorProduct (ULift.{1} R) M N) :
    LinearMap.rTensor Q f (LinearMap.lTensor M g x) = LinearMap.lTensor P g (LinearMap.rTensor N f x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

theorem tres_comp (X Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {W V U : Scheme.{0}} (m : W ⟶ V) (k : V ⟶ U)
    (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map (m ≫ k).op).hom (Y.map (m ≫ k).op).hom x =
      TensorProduct.map (X.map m.op).hom (Y.map m.op).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem nat_apply {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U)
    (a : X.obj (op U)) : (Z.map k.op).hom ((ψ.app (op U)).hom a) = (ψ.app (op V)).hom ((X.map k.op).hom a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (ψ.naturality k.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem tres_rTensor {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (Z.map k.op).hom (Y.map k.op).hom (LinearMap.rTensor _ (ψ.app (op U)).hom x) =
      LinearMap.rTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tres_lTensor (X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {Y Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    (ψ : Y ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map k.op).hom (Z.map k.op).hom (LinearMap.lTensor _ (ψ.app (op U)).hom x) =
      LinearMap.lTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ker_tensor_loc {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C)
    (hex : ∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (W : Scheme.{0})
    (z : TensorProduct (ULift.{1} R) (LinearMap.ker (g.hom.app (op W)).hom) (P.obj (op W))) :
    Loc W fun W' n => ∃ y : TensorProduct (ULift.{1} R) (Sec A W') (P.obj (op W')),
      LinearMap.rTensor _ (f.hom.app (op W')).hom y = TensorProduct.map (B.obj.map n.op).hom (P.map n.op).hom
        (LinearMap.rTensor _ (LinearMap.ker (g.hom.app (op W)).hom).subtype z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact loc_of_forall W _ fun W' n => ⟨0, by simp⟩
  | tmul b p =>
    refine loc_mono W _ _ (hex W b.1 (LinearMap.mem_ker.mp b.2)) ?_
    rintro W' n ⟨a, ha⟩
    refine ⟨a ⊗ₜ (P.map n.op).hom p, ?_⟩
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, Submodule.coe_subtype]
    exact congrArg (· ⊗ₜ[ULift.{1} R] (P.map n.op).hom p) ha
  | add z₁ z₂ h₁ h₂ =>
    refine loc_mono W _ _ (loc_and W _ _ h₁ h₂) ?_
    rintro W' n ⟨⟨y₁, e₁⟩, ⟨y₂, e₂⟩⟩
    exact ⟨y₁ + y₂, by simp only [map_add, e₁, e₂]⟩

end TensFlat

open TensFlat in

theorem tensor_flat_loc_exact : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  intro R _ M hM A B C f g _ hex U x hx
  obtain ⟨P, φ, hsurj, hinj, hflat⟩ := hM
  have h1 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R B.obj P M.obj φ hsurj hinj U).1 x
  apply loc_trans
  refine loc_mono U _ _ (loc_and U _ _ h1 hx) ?_
  rintro V k ⟨⟨x', hx'⟩, hz⟩
  have hz0 : LinearMap.lTensor _ (φ.app (op V)).hom (LinearMap.rTensor _ (g.hom.app (op V)).hom x') = 0 := by
    rw [← rl_comm, hx']
    exact hz
  have h2 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R C.obj P M.obj φ hsurj hinj V).2 _ hz0
  apply loc_trans
  refine loc_mono V _ _ h2 ?_
  intro W m hm
  have hg0 : LinearMap.rTensor _ (g.hom.app (op W)).hom
      (TensorProduct.map (B.obj.map m.op).hom (P.map m.op).hom x') = 0 := by
    rw [← tres_rTensor]; exact hm
  by_cases hW : Nonempty W
  · haveI := hflat W hW
    have hexact := Module.Flat.rTensor_exact (P.obj (op W))
      (LinearMap.exact_subtype_ker_map (g.hom.app (op W)).hom)
    obtain ⟨z, hzx⟩ := (hexact _).mp hg0
    refine loc_mono W _ _ (ker_tensor_loc f g hex P W z) ?_
    rintro W' n ⟨y, hy⟩
    refine ⟨LinearMap.lTensor _ (φ.app (op W')).hom y, ?_⟩
    rw [rl_comm, hy, hzx, tres_comp, tres_comp, ← hx', tres_lTensor, tres_lTensor]
  · haveI : IsEmpty W := not_nonempty_iff.mp hW
    exact loc_of_isEmpty W _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem theta_tensor_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p),
    IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (σ : Λ →+* O),
    ∃ f : RL p O Λ →+* O, IsTheta σ f ∧ Function.Surjective f ∧ f (inA (xi ε)) = 0 ∧
      f (inA (nu ε)) ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ σ
  obtain ⟨-, -, hker, hsurj, hnu, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  letI : Algebra ℤ_[p] O := (padicToO p O).toAlgebra
  let θ' : Ainf p O →ₐ[ℤ_[p]] O :=
    { WittVector.fontaineTheta O p with commutes' := fun r => rfl }
  have hσ : σ.comp (algebraMap ℤ_[p] Λ) = padicToO p O := GlobalTheory.T.padic_ring_hom_eq_canonical p O _
  have hσr : ∀ r : ℤ_[p], σ (algebraMap ℤ_[p] Λ r) = algebraMap ℤ_[p] O r := fun r => by
    rw [← RingHom.comp_apply, hσ]; rfl
  let σ' : Λ →ₐ[ℤ_[p]] O := { σ with commutes' := hσr }
  let f := (Algebra.TensorProduct.productMap θ' σ').toRingHom
  have hf : ∀ (a : Ainf p O) (l : Λ), f (a ⊗ₜ l) = WittVector.fontaineTheta O p a * σ l := by
    intro a l
    simp [f, θ', σ', Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  have hA : ∀ a : Ainf p O, f (inA a) = WittVector.fontaineTheta O p a := by
    intro a
    show f (algebraMap (Ainf p O) (RL p O Λ) a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, hf]
    simp
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨inA a, hA a⟩
  · rw [hA]
    have : xi ε ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
      rw [hker]; exact Ideal.subset_span rfl
    exact this
  · rw [hA]; exact hnu

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralScheStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme : ∀ (F : Type) [Field F] (X V : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ] [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  first | exact @GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | exact GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | (intros; apply GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmas
section
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.TowerLift

theorem closed_lift (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hdc : ∀ n x, d n (c n x) = 0) (hsc : ∀ n x, s n (c (n + 1) x) = c n (r n x)) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x))
    (hr : ∀ n, Function.Surjective (r n)) (hcl : ∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w)
    (b : ∀ n, B n) (hb : ∀ n, t n (b (n + 1)) = b n) (hrg : ∀ n, ∃ a, d n a = b n) :
    ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n := by
  have step : ∀ n (x : {a : A n // d n a = b n}), ∃ y : {a : A (n + 1) // d (n + 1) a = b (n + 1)}, s n y.1 = x.1 := by
    intro n x
    obtain ⟨x', hx'⟩ := hrg (n + 1)
    have h0 : d n (x.1 - s n x') = 0 := by
      rw [map_sub, x.2, ← htd, hx', hb, sub_self]
    obtain ⟨a', w, ha', hw⟩ := hcl n _ h0
    obtain ⟨w', rfl⟩ := hr n w
    refine ⟨⟨x' + a' + c (n + 1) w', ?_⟩, ?_⟩
    · rw [map_add, map_add, hx', ha', hdc, add_zero, add_zero]
    · show s n (x' + a' + c (n + 1) w') = x.1
      rw [map_add, map_add, hsc, add_assoc, ← hw, add_sub_cancel]
  choose f hf using step
  obtain ⟨a₀, ha₀⟩ := hrg 0
  let g : ∀ n, {a : A n // d n a = b n} := fun n => Nat.rec ⟨a₀, ha₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, fun n => hf n (g n), fun n => (g n).2⟩

theorem closed_extend (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hd : ∀ n x, d n x ∈ Z n) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x)) (hs : ∀ n, Function.Surjective (s n))
    (hZ : ∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) (hl : ∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) :
    ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  intro b₀ hb₀
  have step : ∀ n (x : Z n), ∃ y : Z (n + 1), t n y.1 = x.1 := by
    intro n x
    obtain ⟨b', hb', a, ha⟩ := hl n x.1 x.2
    obtain ⟨a'', rfl⟩ := hs n a
    refine ⟨⟨b' + d (n + 1) a'', (Z (n + 1)).add_mem hb' (hd _ _)⟩, ?_⟩
    show t n (b' + d (n + 1) a'') = x.1
    rw [map_add, htd, ha]
  choose f hf using step
  let g : ∀ n, Z n := fun n => Nat.rec ⟨b₀, hb₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, rfl, fun n => (g n).2, fun n => hf n (g n)⟩

theorem tower_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n :=
  ⟨closed_lift, closed_extend⟩

end GlobalTheory.TowerLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCompPosOfAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.UPel.HT

theorem trace_comp_pos_of_adjoint {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u)
    (T T' : V →ₗ[ℝ] V) (hadj : ∀ u v, g (T u) v = g u (T' v)) (hT' : T' ≠ 0) :
    0 < LinearMap.trace ℝ V (T ∘ₗ T') := by
  letI core : InnerProductSpace.Core ℝ V :=
    { inner := fun x y => g x y
      conj_inner_symm := fun x y => by simpa using hs y x
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · simpa using (hp x h).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hp x h).ne' hx }
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b]
  have key : ∀ i, ⟪b i, (T ∘ₗ T') (b i)⟫_ℝ = g (T' (b i)) (T' (b i)) := by
    intro i
    show g (b i) (T (T' (b i))) = _
    rw [hs, hadj]
  simp only [key]
  have hnn : ∀ i, 0 ≤ g (T' (b i)) (T' (b i)) := fun i => by
    by_cases h : T' (b i) = 0
    · simp [h]
    · exact (hp _ h).le
  obtain ⟨i, hi⟩ : ∃ i, T' (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hT'
    exact b.toBasis.ext (fun i => by simpa using h i)
  exact Finset.sum_pos' (fun i _ => hnn i) ⟨i, Finset.mem_univ _, hp _ hi⟩

theorem trace_mul_star_pos : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), x ≠ 0 →
    0 < LinearMap.trace ℤ D.La (DistribMulAction.toLinearMap ℤ D.La (x * (D.star x).unop)) := by
  intro p _ D x hx
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, hJJ, hJinv, hpos, hcomm, -⟩ := D.dom
  let A : D.O → (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) := fun b =>
    (DistribMulAction.toLinearMap ℤ D.La b).baseChange ℝ
  have hcomp : A x ∘ₗ A (D.star x).unop =
      (DistribMulAction.toLinearMap ℤ D.La (x * (D.star x).unop)).baseChange ℝ := by
    clear hcomm hpos hJinv hJJ
    simp only [A]
    rw [← LinearMap.baseChange_comp]
    congr 1
    ext y
    show x • ((D.star x).unop • y) = (x * (D.star x).unop) • y
    rw [mul_smul]
  have hA : ∀ b (r : ℝ) (y : D.La), A b (r ⊗ₜ y) = r ⊗ₜ (b • y) := fun _ _ _ => rfl
  have hAJ : ∀ b, J ∘ₗ A b = A b ∘ₗ J := fun b => hcomm b (A b) (fun y => rfl)
  have hEF : ∀ y z : D.La, D.EF y z = - D.EF z y := by
    intro y z
    have h := D.alt (y + z)
    simp only [map_add, LinearMap.add_apply, D.alt y, D.alt z, zero_add, add_zero] at h
    omega
  have hanti : ∀ u v, D.EF.baseChange ℝ u v = - D.EF.baseChange ℝ v u := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hEF y z]
        simp only [zsmul_eq_mul, Int.cast_neg]
        ring
      | add v w hv hw =>
        simp only [map_add, LinearMap.add_apply]
        rw [hv, hw]
        ring
    | add u w hu hw =>
      simp only [map_add, LinearMap.add_apply]
      rw [hu, hw]
      ring
  have hadjB : ∀ b u v, D.EF.baseChange ℝ (A b u) v = D.EF.baseChange ℝ u (A (D.star b).unop v) := by
    intro b u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [hA, hA, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, D.adj]
      | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw]
    | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  have hsym : ∀ u v, D.EF.baseChange ℝ (J u) v = D.EF.baseChange ℝ (J v) u := by
    intro u v
    rw [← hJinv (J v) u, hJJ, map_neg, LinearMap.neg_apply, hanti v (J u), neg_neg]
  have hadjg : ∀ u v, (D.EF.baseChange ℝ ∘ₗ J) (A x u) v =
      (D.EF.baseChange ℝ ∘ₗ J) u (A (D.star x).unop v) := by
    intro u v
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply J (A x), hAJ, LinearMap.comp_apply, hadjB]
  have hinj : ∀ y : D.La, (1 : ℝ) ⊗ₜ[ℤ] y = 0 → y = 0 := by
    intro y hy
    refine (Module.forall_dual_apply_eq_zero_iff ℤ y).1 fun φ => ?_
    have h := congrArg (fun t => TensorProduct.rid ℤ ℝ (LinearMap.baseChange ℝ φ t)) hy
    simp only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, map_zero] at h
    simpa using h
  have hT' : A (D.star x).unop ≠ 0 := by
    intro h0
    apply hx
    have hz : ∀ y : D.La, (D.star x).unop • y = 0 := fun y => hinj _ (by
      have := LinearMap.congr_fun h0 ((1 : ℝ) ⊗ₜ y)
      rwa [hA, LinearMap.zero_apply] at this)
    have h1 := GlobalTheory.T.harrisTaylor_order_faithful_lattice p D _ hz
    rw [← D.star_star x, h1]
    simp
  have htr := trace_comp_pos_of_adjoint (D.EF.baseChange ℝ ∘ₗ J)
    (fun u v => by simp only [LinearMap.comp_apply]; exact hsym u v)
    (fun u hu => by simpa only [LinearMap.comp_apply] using hpos u hu)
    (A x) (A (D.star x).unop) hadjg hT'
  rw [hcomp, LinearMap.trace_baseChange] at htr
  simpa using htr

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransformStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_residuallyUnipotent_cayleyTransform : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ, algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 → (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧ Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any | exact GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any | (intros; apply GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any <;> assumption)
end

