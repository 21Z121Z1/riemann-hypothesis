import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0491
import Development.EtaleCohomology.EtaleSheaves.Bundle0056
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0006
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0012
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0027
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0024
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0025
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0020
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0026
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0023

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicMappingConeChainsOfHomAcyclicFree
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

section Cone

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
  (comm : φ₁ ≫ b = a ≫ φ₂)

private theorem inl_map (n m : ℤ) (h : m + (-1) = n) :
    (mappingCone.inl φ₁).v m n h ≫ (mappingCone.map φ₁ φ₂ a b comm).f n =
      a.f m ≫ (mappingCone.inl φ₂).v m n h := by
  simp [mappingCone.map, Cochain.zero_cochain_comp_v]

private theorem inr_map (n : ℤ) :
    (mappingCone.inr φ₁).f n ≫ (mappingCone.map φ₁ φ₂ a b comm).f n =
      b.f n ≫ (mappingCone.inr φ₂).f n := by
  simp [mappingCone.map]

private theorem map_fst (n m : ℤ) (h : n + 1 = m) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.fst φ₂).1.v n m h =
      (mappingCone.fst φ₁).1.v n m h ≫ a.f m := by
  rw [mappingCone.ext_from_iff φ₁ m n h]
  constructor
  · rw [reassoc_of% (inl_map φ₁ φ₂ a b comm n m (by omega))]
    simp
  · rw [reassoc_of% (inr_map φ₁ φ₂ a b comm n)]
    simp

private theorem map_snd (n : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.snd φ₂).v n n (add_zero n) =
      (mappingCone.snd φ₁).v n n (add_zero n) ≫ b.f n := by
  rw [mappingCone.ext_from_iff φ₁ (n + 1) n rfl]
  constructor
  · rw [reassoc_of% (inl_map φ₁ φ₂ a b comm n (n + 1) (by omega))]
    simp
  · rw [reassoc_of% (inr_map φ₁ φ₂ a b comm n)]
    simp

end Cone

variable {B : Scheme.{0}}

private def famCh (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) : B.Etale ⥤ Cx (ZMod q) := G ⋙ sch ⋙ chains (ZMod q)

private def termIso (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) (p : ℕ) :
    G ⋙ yoneda ⋙ free (ZMod q) ≅ famCh q G ⋙ HomologicalComplex.eval _ _ (-(p : ℤ)) :=
  NatIso.ofComponents (fun U => (chainsXIso (ZMod q) (sch.obj (G.obj U)) p).symm) (by
    intro U V a
    exact (GlobalTheory.EtC.HCTerms.chainsXIso_inv_map (ZMod q) (sch.map (G.map a)) p).symm)

private theorem famCh_good (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) (h : Good (G ⋙ yoneda ⋙ free (ZMod q))) (n : ℤ) :
    Good (famCh q G ⋙ HomologicalComplex.eval _ _ n) := by
  obtain ⟨hiso, hzero, -⟩ := UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B
  rcases lt_or_ge 0 n with hn | hn
  · exact hzero _ fun U => GlobalTheory.EtC.HCTerms.isZero_chains_X (ZMod q) _ n hn
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    exact hiso _ _ ⟨termIso q G p⟩ h

private theorem cone_comm {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) {U V : B.Etale} (a : U ⟶ V) :
    (chains (ZMod q)).map (sch.map (F.app U)) ≫ (chains (ZMod q)).map (sch.map (G₂.map a)) =
      (chains (ZMod q)).map (sch.map (G₁.map a)) ≫ (chains (ZMod q)).map (sch.map (F.app V)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, F.naturality]

private def coneI₁ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    famCh q G₁ ⋙ HomologicalComplex.eval _ _ (n + 1) ⟶ coneF F q ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.inl ((chains (ZMod q)).map (sch.map (F.app U)))).v (n + 1) n (by omega)
  naturality U V a := (inl_map ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n (n + 1) (by omega)).symm

private def coneR₁ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    coneF F q ⋙ HomologicalComplex.eval _ _ n ⟶ famCh q G₁ ⋙ HomologicalComplex.eval _ _ (n + 1) where
  app U := (mappingCone.fst ((chains (ZMod q)).map (sch.map (F.app U)))).1.v n (n + 1) rfl
  naturality U V a := map_fst ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n (n + 1) rfl

private def coneI₂ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    famCh q G₂ ⋙ HomologicalComplex.eval _ _ n ⟶ coneF F q ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.inr ((chains (ZMod q)).map (sch.map (F.app U)))).f n
  naturality U V a := (inr_map ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n).symm

private def coneR₂ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    coneF F q ⋙ HomologicalComplex.eval _ _ n ⟶ famCh q G₂ ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.snd ((chains (ZMod q)).map (sch.map (F.app U)))).v n n (add_zero n)
  naturality U V a := map_snd ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n

theorem UpperTheory.homAcyclic_mappingCone_chains_of_homAcyclic_free :
    ∀ (q : ℕ) {B : Scheme.{0}} {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂), Good (G₁ ⋙ yoneda ⋙ free (ZMod q)) → Good (G₂ ⋙ yoneda ⋙ free (ZMod q)) → (∀ n : ℤ, Good (coneF F q ⋙ HomologicalComplex.eval _ _ n)) ∧ ∀ (U : B.Etale) (n : ℤ), 0 < n → IsZero (((coneF F q).obj U).X n) := by
  intro q B G₁ G₂ F h₁ h₂
  refine ⟨fun n => ?_, fun U n hn => ?_⟩
  · refine (UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B).2.2 _ _ _ (coneI₁ F q n) (coneR₁ F q n) (coneI₂ F q n) (coneR₂ F q n)
      ?_ ?_ ?_ ?_ ?_ (famCh_good q G₁ h₁ (n + 1)) (famCh_good q G₂ h₂ n)
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.inl_v_fst_v ((chains (ZMod q)).map (sch.map (F.app U))) (n + 1) n rfl
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.inr_f_snd_v ((chains (ZMod q)).map (sch.map (F.app U))) n
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact mappingCone.inl_v_snd_v ((chains (ZMod q)).map (sch.map (F.app U))) (n + 1) n (by omega)
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact mappingCone.inr_f_fst_v ((chains (ZMod q)).map (sch.map (F.app U))) n (n + 1) rfl
    · ext U : 2
      rw [NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.id_X ((chains (ZMod q)).map (sch.map (F.app U))) n (n + 1) rfl
  · exact (mappingCone.isZero_X_iff ((chains (ZMod q)).map (sch.map (F.app U))) n).2
      ⟨GlobalTheory.EtC.HCTerms.isZero_chains_X _ _ _ (by omega), GlobalTheory.EtC.HCTerms.isZero_chains_X _ _ _ hn⟩

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.KumSExact
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Deg2

abbrev T (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def kap (q : ℕ) [NeZero q] : T q ⟶ Gm := (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose

theorem kap_spec (q : ℕ) [NeZero q] : Mono (kap q) ∧ kap q ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map (kap q) (show Sec (T q) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map (kap q) a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b :=
  (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose_spec

def Cq (q : ℕ) [NeZero q] : Shv ℤ := cokernel (kap q)

def piq (q : ℕ) [NeZero q] : Gm ⟶ Cq q := cokernel.π (kap q)

def powq (q : ℕ) [NeZero q] : Cq q ⟶ Gm := cokernel.desc (kap q) ((q : ℤ) • 𝟙 Gm) (kap_spec q).2.1

def kumS (q : ℕ) [NeZero q] : ShortComplex (Shv ℤ) := ShortComplex.mk (kap q) (piq q) (cokernel.condition (kap q))

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

section MV
variable (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)

theorem mvS_zero : biprod.lift ((chains R).map (spMap (Localization.awayMap (algebraMap A A') f)))
      (-(chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ≫
    biprod.desc ((chains R).map (spMap (algebraMap A (Localization.Away f))))
      ((chains R).map (spMap (algebraMap A A'))) = 0 := by
  have h : (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
    IsLocalization.map_comp _
  have e1 := (chains R).map_comp (spMap (Localization.awayMap (algebraMap A A') f)) (spMap (algebraMap A (Localization.Away f)))
  have e2 := (chains R).map_comp (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) (spMap (algebraMap A A'))
  rw [spMap_comp] at e1 e2
  rw [biprod.lift_desc, Preadditive.neg_comp, ← e1, ← e2, h]
  simp

def mvS : ShortComplex (Cx R) := ShortComplex.mk _ _ (mvS_zero R A A' f)

end MV

section Shrink
variable (R : Type) [CommRing R] (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B)

abbrev LS : Type := Localization.Away (algebraMap B A' s)

theorem rho_unit : IsUnit (((algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp
    (algebraMap A' (LS B A' s))) (algebraMap B A' f)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (LS B A' s) f)) (algebraMap B (LS B A' s) f)
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact h

def rho : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B (LS B A' s) f) :=
  IsLocalization.Away.lift (algebraMap B A' f)
    (g := (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp (algebraMap A' (LS B A' s)))
    (rho_unit B A' f s)

theorem rho_comp : (rho B A' f s).comp (algebraMap A' (Localization.Away (algebraMap B A' f))) =
    (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp (algebraMap A' (LS B A' s)) := by
  unfold rho
  exact IsLocalization.Away.lift_comp (algebraMap B A' f) (rho_unit B A' f s)

theorem rho_away : (rho B A' f s).comp (Localization.awayMap (algebraMap B A') f) =
    Localization.awayMap (algebraMap B (LS B A' s)) f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  have h1 : (Localization.awayMap (algebraMap B A') f).comp (algebraMap B (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap B A' f))).comp (algebraMap B A') := IsLocalization.map_comp _
  have h2 : (Localization.awayMap (algebraMap B (LS B A' s)) f).comp (algebraMap B (Localization.Away f)) =
      (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp (algebraMap B (LS B A' s)) :=
    IsLocalization.map_comp _
  rw [RingHom.comp_assoc, h1, h2, ← RingHom.comp_assoc, rho_comp, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

def mvMor : mvS R B (LS B A' s) f ⟶ mvS R B A' f where
  τ₁ := (chains R).map (spMap (rho B A' f s))
  τ₂ := biprod.map (𝟙 _) ((chains R).map (spMap (algebraMap A' (LS B A' s))))
  τ₃ := 𝟙 _
  comm₁₂ := by
    have e1 := (chains R).map_comp (spMap (rho B A' f s)) (spMap (Localization.awayMap (algebraMap B A') f))
    have e2 := (chains R).map_comp (spMap (rho B A' f s)) (spMap (algebraMap A' (Localization.Away (algebraMap B A' f))))
    have e3 := (chains R).map_comp (spMap (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f)))) (spMap (algebraMap A' (LS B A' s)))
    rw [spMap_comp, rho_away] at e1
    rw [spMap_comp, rho_comp] at e2
    rw [spMap_comp] at e3
    apply biprod.hom_ext
    · simp [mvS, e1]
    · simp only [mvS, Category.assoc, biprod.lift_snd, biprod.map_snd, Preadditive.neg_comp, Preadditive.comp_neg, biprod.lift_snd_assoc]
      rw [← e2, e3]
  comm₂₃ := by
    have e1 := (chains R).map_comp (spMap (algebraMap A' (LS B A' s))) (spMap (algebraMap B A'))
    rw [spMap_comp, ← IsScalarTower.algebraMap_eq] at e1
    apply biprod.hom_ext'
    · simp [mvS]
    · simp [mvS, e1]

end Shrink

end UpperTheory.Deg2
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LiftIdempotentFactorizationHolds
section
noncomputable section

theorem UpperTheory.liftIdempotentFactorization_holds :
    LateralTheory.E.LIdemLiftPf.LFact := by
  intro A _ I _ g hg n m h
  exact UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow A I g hg n m h

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.FullyFaithfulLift

private theorem cancel_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) [F.Faithful] (c c' : J ⥤ C) (h : c ⋙ F = c' ⋙ F) : c = c' := by
  have hob : ∀ j, c.obj j = c'.obj j := fun j => hobj (congrArg (fun G => G.obj j) h)
  refine CategoryTheory.Functor.ext hob ?_
  intro X Y f
  apply F.map_injective
  have e := CategoryTheory.Functor.congr_hom h f
  simp only [CategoryTheory.Functor.comp_map] at e
  rw [e]
  simp [eqToHom_map]

private theorem lift_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    [F.Full] [F.Faithful] (c : J ⥤ D) (l : J → C) (hl : ∀ j, F.obj (l j) = c.obj j) :
    ∃ c' : J ⥤ C, c' ⋙ F = c := by
  refine ⟨{ obj := l
            map := fun {i j} f => F.preimage (eqToHom (hl i) ≫ c.map f ≫ eqToHom (hl j).symm)
            map_id := fun i => F.map_injective (by simp)
            map_comp := fun f g => F.map_injective (by simp) }, ?_⟩
  refine CategoryTheory.Functor.ext hl (fun i j f => ?_)
  simp

private theorem sp_map_eq {E : Spc} {a b : Act} (φ : Act.Hom a b) {k : ℕ} {T : Scheme.{0}} (x : Sx (Sp E a) k T) :
    Sx.map (Sp.map E φ) x = ((x.1, Sx.map (spcMap φ) x.2) : Sx (Sp E b) k T) := rfl

private theorem fn_obj_inj {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (A : CommRingCat.{0}) : Function.Injective (φ.fn A).obj := by
  intro x y h
  have e : φ.d.app A x.pt = φ.d.app A y.pt := congrArg Ob.pt h
  cases x
  cases y
  congr
  exact hi A e

private theorem fn_faithful {a b : Act} (φ : Act.Hom a b) (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g))
    (A : CommRingCat.{0}) : (φ.fn A).Faithful :=
  ⟨fun {_ _} _ _ h => Subtype.ext ((hb A).1 (congrArg Subtype.val h))⟩

private theorem fn_full {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) (A : CommRingCat.{0}) : (φ.fn A).Full := by
  constructor
  intro x y u
  obtain ⟨g, hg⟩ := (hb A).2 u.1
  refine ⟨⟨g, ?_⟩, ?_⟩
  · apply hi A
    have e := φ.eq A g y.pt
    have hg' : φ.g.app A g = u.1 := hg
    rw [hg'] at e
    exact u.2.trans e.symm
  · apply Subtype.ext
    exact hg

private theorem mono_sp (E : Spc) {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Mono (Sp.map E φ) := by
  apply UpperTheory.mono_of_injective_on_simplices
  intro k T x y h
  simp only [sp_map_eq] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  haveI := fn_faithful φ hb Γ(T, ⊤)
  have h2' : (show ComposableArrows (Ob a Γ(T, ⊤)) k from x.2) ⋙ φ.fn Γ(T, ⊤) =
      (show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2) ⋙ φ.fn Γ(T, ⊤) := h2
  exact Prod.ext h1 (cancel_comp (φ.fn Γ(T, ⊤)) (fn_obj_inj φ hi _) _ _ h2')

private theorem lift_sp (E : Spc) {a₁ a : Act} (φ : Act.Hom a₁ a) (hi : ∀ A, Function.Injective (fun x : a₁.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a₁.G.obj A => φ.g.app A g)) {k : ℕ} {W : Scheme.{0}} (y : Sx (Sp E a) k W)
    (y₀ : a₁.D.obj Γ(W, ⊤))
    (h0 : φ.d.app _ y₀ = ((show ComposableArrows (Ob a Γ(W, ⊤)) k from y.2).obj 0).pt) :
    ∃ x : Sx (Sp E a₁) k W, Sx.map (Sp.map E φ) x = y := by
  classical
  set c : ComposableArrows (Ob a Γ(W, ⊤)) k := y.2 with hc
  have hl : ∀ j : Fin (k + 1), ∃ o : Ob a₁ Γ(W, ⊤), (φ.fn Γ(W, ⊤)).obj o = c.obj j := by
    intro j
    have hle : (0 : Fin (k + 1)) ≤ j := Fin.zero_le _
    obtain ⟨u, hu⟩ := c.map (homOfLE hle)
    obtain ⟨g, hg⟩ := (hb Γ(W, ⊤)).2 u⁻¹
    refine ⟨⟨a₁.smul _ g y₀⟩, ?_⟩
    have e := φ.eq Γ(W, ⊤) g y₀
    have hg' : φ.g.app Γ(W, ⊤) g = u⁻¹ := hg
    have h0' : φ.d.app Γ(W, ⊤) y₀ = (c.obj 0).pt := h0
    have key : (c.obj j).pt = φ.d.app Γ(W, ⊤) (a₁.smul _ g y₀) := by
      erw [e, hg', h0', hu, ← a.mul_smul, inv_mul_cancel, a.one_smul]
    exact congrArg Ob.mk key.symm
  choose l hl' using hl
  haveI := fn_full φ hi hb Γ(W, ⊤)
  haveI := fn_faithful φ hb Γ(W, ⊤)
  obtain ⟨c', hc'⟩ := lift_comp (φ.fn Γ(W, ⊤)) c l hl'
  refine ⟨((y.1, show Sx (spc a₁) k W from c') : Sx (Sp E a₁) k W), ?_⟩
  refine (sp_map_eq φ _).trans ?_
  exact Prod.ext rfl hc'

end UpperTheory.FullyFaithfulLift

theorem UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered :
    ∀ (R : Type) [CommRing R] (E : Spc) {a₁ a₂ a : Act} (φ₁ : Act.Hom a₁ a) (φ₂ : Act.Hom a₂ a),
        (∀ A, Function.Injective (fun x : a₁.D.obj A => φ₁.d.app A x)) → (∀ A, Function.Injective (fun x : a₂.D.obj A => φ₂.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a₁.G.obj A => φ₁.g.app A g)) → (∀ A, Function.Bijective (fun g : a₂.G.obj A => φ₂.g.app A g)) →
        (∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Loc T fun V g =>
          (∃ y, φ₁.d.app _ y = a.D.map g.appTop x) ∨ (∃ y, φ₂.d.app _ y = a.D.map g.appTop x)) →
        Cover2 R (Sp.map E φ₁) (Sp.map E φ₂) := by
  intro R _ E a₁ a₂ a φ₁ φ₂ i₁ i₂ b₁ b₂ hl
  refine UpperTheory.mayerVietorisCover_of_mono_of_zariskiLocal R _ _ (UpperTheory.FullyFaithfulLift.mono_sp E φ₁ i₁ b₁) (UpperTheory.FullyFaithfulLift.mono_sp E φ₂ i₂ b₂) (fun k T y => ?_)
  obtain ⟨S, hS, hP⟩ := hl T ((show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2).obj 0).pt
  refine ⟨S, hS, fun W h hh => ?_⟩
  rcases hP W h hh with ⟨y₀, e⟩ | ⟨y₀, e⟩
  · exact Or.inl (UpperTheory.FullyFaithfulLift.lift_sp E φ₁ i₁ b₁ (y.res h) y₀ e)
  · exact Or.inr (UpperTheory.FullyFaithfulLift.lift_sp E φ₂ i₂ b₂ (y.res h) y₀ e)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplicativeGroupOneCocycleEtaleLocallyCobound
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma sec_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  change (ModuleCat.Hom.hom (F.obj.map k.op)) ((ModuleCat.Hom.hom (F.obj.map g.op)) a) = (ModuleCat.Hom.hom (F.obj.map (k ≫ g).op)) a
  rw [op_comp, Functor.map_comp]
  rfl

private lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (a : Sec F U) : Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom a) h

theorem UpperTheory.multiplicativeGroup_oneCocycle_etaleLocally_coboundary :
    ∀ (A : Type) [CommRing A] (z : Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of A))),
        Sec.map ((res ℤ Gm).d 1 2) z = 0 →
        ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
          ∃ w : Sec ((res ℤ Gm).X 0) (Spec (CommRingCat.of C)),
            Sec.map ((res ℤ Gm).d 0 1) w = Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) z := by
  intro A _ z hz
  have hloc := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec (CommRingCat.of A))).2.2.1 0 1 2 (by norm_num) (by norm_num) z (by norm_num) hz
  have hstab : ∀ (V W : Scheme) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V),
      (∃ y, Sec.map ((res ℤ Gm).d 0 1) y = Sec.res g z) →
      (∃ y, Sec.map ((res ℤ Gm).d 0 1) y = Sec.res (k ≫ g) z) := by
    rintro V W g k ⟨y, hy⟩
    exact ⟨Sec.res k y, by rw [sec_map_res, hy, sec_res_res]⟩
  obtain ⟨n, C, hC, hA, het, hff, hP⟩ := UpperTheory.exists_finite_etale_faithfullyFlat_cover_of_etaleLocal_affine A _ hstab hloc
  obtain ⟨w, hw⟩ := (UpperTheory.sections_specPi_bijective_prod_sections ℤ ((res ℤ Gm).X 0) n C).2 (fun i => (hP i).choose)
  refine ⟨(i : Fin n) → C i, inferInstance, inferInstance, hff, het, w, ?_⟩
  apply (UpperTheory.sections_specPi_bijective_prod_sections ℤ ((res ℤ Gm).X 1) n C).1
  funext i
  have hwi := congrFun hw i
  dsimp only at hwi
  show Sec.res _ (Sec.map _ w) = Sec.res _ (Sec.res _ z)
  rw [← sec_map_res, hwi, (hP i).choose_spec, sec_res_res, ← Spec.map_comp]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ProductLevelwiseOfAlexanderWhitney
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem key (aw : LeafAW) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc}
    (π : E ⟶ sch.obj X) (m j i : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X)
    (hβ : IsRep U β c.1)
    (Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom
      (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m))
    (hP : IsProd (twPair q i j) π β Φ) (hO : Φ.Ok) :
    (∀ n : ℤ, Function.Bijective fun a : Ht q E n i =>
      Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)) ↔ Φ.TotEx := by
  exact UpperTheory.bijective_iff_totalQuasiIso_of_totalModels _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO
    (fun n => Ht q E n i) (fun n => ↥(Hs q (abv U π) (n + m) (i + j)))
    (fun n x a => HRel x a) (fun n x b => SRel x (b : Ht q (dbl (abv U π)) (n + m) (i + j)))
    (fun n a => Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c))
    (fun n => UpperTheory.supportDoubleComplex_bot_totalModel _ _ _ n) (fun n => UpperTheory.relativeCohomology_isTotalModel_of_image q (abv U π) (i + j) m n (n + m) rfl)
    (fun n x a h => UpperTheory.relativeCupProduct_realizes_product_of_representative aw q U π m j i n c β hβ Φ hP x a h)

theorem UpperTheory.productLevelwise_of_alexanderWhitney :
    LeafAW → LeafPrdLevel := by
  intro aw _ q _ X U E π m j c hlev n i
  obtain ⟨β, hβ⟩ := UpperTheory.exists_section_representing_relativeClass q X U m j c
  obtain ⟨Φ, hP, hO⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U π m β hβ.1 hβ.2.1
  have hT : Φ.TotEx := by
    refine UpperTheory.totalExact_of_columnExact _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO ?_
    intro p
    obtain ⟨Ψ, hPΨ, hOΨ⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U
      (disc.map (π.app (op { len := p }))) m β hβ.1 hβ.2.1
    refine UpperTheory.relativeCupProduct_levelwise_compat _ (twPair q i j) U π m β p Φ Ψ hP hPΨ ?_
    exact (key aw q U (disc.map (π.app (op { len := p }))) m j i c β hβ Ψ hPΨ hOΨ).1
      (fun n' => hlev (op { len := p }) n' i)
  exact (key aw q U π m j i c β hβ Φ hP hO).2 hT n
end

