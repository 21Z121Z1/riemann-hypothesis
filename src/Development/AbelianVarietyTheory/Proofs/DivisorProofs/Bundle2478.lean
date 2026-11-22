import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

noncomputable section
namespace GlobalTheory.Poinc

theorem exists_eq_div_of_mem_O_affine : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z ∈ U, ∀ x ∈ M.O z, ∃ a ∈ M.ringOn (U : Set M.Z), ∃ b ∈ M.ringOn (U : Set M.Z), b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x = a / b := by
  intro o Ω _ _ _ M U hU z hz x hx
  obtain ⟨W, f, hzW, rfl⟩ := hx
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgW, hzg⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzg⟩
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgW f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, U), M.res _ hg (algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen g) t) = M.res U hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_resG, res_apply, ← map_pow, res_apply, res_apply] at h1
  have hu := (isUnit_O_iff _).1 ((isUnit_valF_iff hz g).2 hzg)
  have hb : valF M.pt U (g ^ n) = valF M.pt U g ^ n := by
    rw [← M.res_apply U hne, map_pow, res_apply]
  have h0 : valF M.pt U (g ^ n) ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ hu.1
  refine ⟨_, (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _, (mem_ringOn_iff_exists hne).2 ⟨g ^ n, rfl⟩, h0, ?_,
    (eq_div_iff h0).2 h1⟩
  rw [hb, ← inv_pow]
  exact pow_mem hu.2 n

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMumfordBundleInvPullbackPrimitiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  first | exact @GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | exact GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | (intros; apply GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsAdaptedToQuotientGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_adapted_to_quotient_generators : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  first | exact @GlobalTheory.pinch_gens_adapted | exact GlobalTheory.pinch_gens_adapted | (intros; apply GlobalTheory.pinch_gens_adapted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.GenFibre

theorem exists_generic_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  intro g n o _ ζ F T W _ _ f fK hfK
  have hsq : spMap fK ≫ jK T.V = jK W ≫ spMap f := by
    have h : fK.comp (algebraMap T.V (FractionRing T.V)) = (algebraMap W (FractionRing W)).comp f := RingHom.ext hfK
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]
  have gB := ((isGrpPullback_pullback ((Over.pullback (spMap f)).obj T.G) (jK W)).comp
    (isGrpPullback_pullback T.G (spMap f))).congr hsq.symm rfl
  have he := isGrpPullback_pullback T.G (jK T.V)
  set B := (Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)
  have w : (pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f)) ≫ T.G.hom =
      (B.hom ≫ spMap fK) ≫ jK T.V := by
    rw [Category.assoc B.hom]; exact gB.1.w
  obtain ⟨α, h₁, h₂⟩ : ∃ α : B.left ⟶ ((Over.pullback (jK T.V)).obj T.G).left,
      α ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) ∧
      α ≫ ((Over.pullback (jK T.V)).obj T.G).hom = B.hom ≫ spMap fK :=
    ⟨he.1.lift _ _ w, he.1.lift_fst _ _ _, he.1.lift_snd _ _ _⟩
  have gα := he.cancel (gB.congr rfl h₁.symm) h₂
  haveI := T.U.gen_hom
  refine ⟨α ≫ T.U.gen.hom.left, (gα.comp (isGrpPullback_of_iso T.U.gen)).congr (Category.comp_id _) rfl, ?_⟩
  rw [Category.assoc, ← Category.assoc T.U.gen.hom.left, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]
  exact h₁

end GlobalTheory.Poinc.GenFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPtSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem exists_geomPt_specializes (R : Type) [CommRing R] (R₁ : Subring R) (p : Sp R₁) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ Sp R), ∀ u, (z ≫ spMap R₁.subtype) u ⤳ p := by
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  obtain ⟨K, _, _, t, ht⟩ := GlobalTheory.SiegelTypings.exists_geomPt (S := Sp R) ⟨P, hP⟩
  refine ⟨K, inferInstance, inferInstance, t, fun u => ?_⟩
  have e : t u = ⟨P, hP⟩ := by
    obtain ⟨v, hv⟩ := ht
    rw [Subsingleton.elim u v, hv]
  rw [Scheme.Hom.comp_apply, e]
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  show P.comap R₁.subtype ≤ p.asIdeal
  rw [hPq]
  exact hqp

section Labels

variable {h M : ℕ}

def toStd : (Fin (h + h) → ZMod M) →+ IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M where
  toFun c := (fun i => c (Fin.castAdd h i), fun i => c (Fin.natAdd h i))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toStd_append (a : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) : toStd (Fin.append a.1 a.2) = a :=
  Prod.ext (funext fun i => Fin.append_left a.1 a.2 i) (funext fun i => Fin.append_right a.1 a.2 i)

theorem append_toStd (c : Fin (h + h) → ZMod M) : Fin.append (toStd c).1 (toStd c).2 = c :=
  Fin.append_castAdd_natAdd

theorem toStd_injective : Function.Injective (toStd (h := h) (M := M)) := fun c c' e => by
  rw [← append_toStd c, ← append_toStd c', e]

theorem sum_val_smul [NeZero M] (c : Fin (h + h) → ZMod M) :
    ∑ i, (c i).val • toStd (Pi.single i (1 : ZMod M)) = toStd c := by
  simp_rw [← map_nsmul, ← map_sum]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul, nsmul_eq_mul, _root_.mul_one, ZMod.natCast_zmod_val]

end Labels

section Sections

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem lv_zero (add : ∀ a b, lv (a + b) = lv a * lv b) : lv 0 = 1 := by
  have e := add 0 0
  rw [add_zero] at e
  exact left_eq_mul.1 e

theorem lv_nsmul (add : ∀ a b, lv (a + b) = lv a * lv b) (n : ℕ) (a) : lv (n • a) = lv a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lv_zero add]
  | succ n ih => rw [succ_nsmul, add, ih, pow_succ]

theorem lv_pow (add : ∀ a b, lv (a + b) = lv a * lv b) (a) : lv a ^ M = 1 := by
  rw [← lv_nsmul add, show M • a = 0 by ext i <;> simp, lv_zero add]

theorem linComb_lv (add : ∀ a b, lv (a + b) = lv a * lv b) {T : Over S} (g : T ⟶ 𝟙_ (Over S)) :
    ∀ {r : ℕ} (v : Fin r → IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) (n : Fin r → ℕ),
      Out.linComb (fun i => g ≫ lv (v i)) n = g ≫ lv (∑ i, n i • v i) := by
  intro r
  induction r with
  | zero =>
    intro v n
    simp [Out.linComb, lv_zero add]
  | succ r ih =>
    intro v n
    have e := ih (fun i => v i.succ) (fun i => n i.succ)
    simp only [Out.linComb] at e ⊢
    rw [List.ofFn_succ, List.prod_cons, e, Fin.sum_univ_succ, add, MonObj.comp_mul, lv_nsmul add,
      MonObj.comp_pow]

end Sections

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

section Cond

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem cond_iff [NeZero M] (add : ∀ a b, lv (a + b) = lv a * lv b) {k : Type} [Field k] (x : Sp k ⟶ S) :
    ((Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) ↔
    ∀ y : Over.mk x ⟶ A, y ^ M = 1 → ∃! c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) = y := by
  have E : ∀ c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) =
        toUnit (Over.mk x) ≫ lv (toStd c) := fun c =>
    (linComb_lv add (toB x) _ _).trans (by rw [sum_val_smul]; rfl)
  have tors : ∀ a, (toUnit (Over.mk x) ≫ lv a) ^ M = 1 := fun a => by
    rw [← MonObj.comp_pow, lv_pow add, MonObj.comp_one]
  constructor
  · rintro ⟨inj, sp⟩ y hy
    obtain ⟨a, rfl⟩ := (sp y).1 hy
    refine ⟨Fin.append a.1 a.2, by beta_reduce; rw [E, toStd_append], fun c hc => toStd_injective ?_⟩
    rw [toStd_append]
    exact inj ((E c).symm.trans hc)
  · intro H
    refine ⟨fun a b e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
    · obtain ⟨c, -, hc⟩ := H _ (tors a)
      have ea := hc (Fin.append a.1 a.2) (by beta_reduce; rw [E, toStd_append])
      have eb := hc (Fin.append b.1 b.2) (by beta_reduce; rw [E, toStd_append]; exact e.symm)
      rw [← toStd_append a, ← toStd_append b, ea, eb]
    · obtain ⟨c, hc, -⟩ := H g hg
      exact ⟨toStd c, (E c).symm.trans hc⟩
    · rintro ⟨a, rfl⟩
      exact tors a

end Cond

section Transfer

variable {h M : ℕ} {S S₁ : Scheme.{0}} {A : Over S} [GrpObj A] {A₁ : Over S₁} [GrpObj A₁] {f : S ⟶ S₁}
  {φ : A.left ⟶ A₁.left} {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}
  {lv₁ : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S₁) ⟶ A₁)}

theorem push_lv (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) (T : Over S) (a) :
    pushHom hp T (toUnit T ≫ lv a) = toUnit (Over.mk (T.hom ≫ f)) ≫ lv₁ a := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (lv a).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ (lv₁ a).left
  rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem cond_push (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) {k : Type} [Field k]
    (x : Sp k ⟶ S)
    (H : (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) :
    (Function.Injective fun a => toUnit (Over.mk (x ≫ f)) ≫ lv₁ a) ∧
      ∀ g : Over.mk (x ≫ f) ⟶ A₁, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk (x ≫ f)) ≫ lv₁ a = g := by
  have P := push_lv hp hl (Over.mk x)
  have inj := push_injective hp (Over.mk x)
  refine ⟨fun a b e => H.1 (inj ?_), fun g => ?_⟩
  · rw [P, P]
    exact e
  · obtain ⟨g', rfl⟩ := push_surjective hp (Over.mk x) g
    rw [← map_pow, ← map_one (pushHom hp (Over.mk x)), inj.eq_iff, H.2 g']
    refine exists_congr fun a => ?_
    rw [← inj.eq_iff, P]
    rfl

end Transfer

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem isLevel_of_subring : ∀ (h M : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ : A.left ⟶ A₁.left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → IsUnit (M : R₁) → IsAbelianScheme A₁ → IsGrpPullback A A₁ (spMap R₁.subtype) φ → (∀ a, (lv a).left ≫ φ = spMap R₁.subtype ≫ (lv₁ a).left) → (∀ a b, lv₁ (a + b) = lv₁ a * lv₁ b) → IsLevel A lv → IsLevel A₁ lv₁ := by
  intro h M R _ R₁ A _ A₁ _ φ lv lv₁ hM hu hA hp hl hadd hlev
  haveI : NeZero M := ⟨hM.ne'⟩
  have hu' : IsUnit ((M : ℕ) : Γ(Sp R₁, ⊤)) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  refine ⟨hadd, fun k _ _ x => (cond_iff hadd x).2 fun y hy => ?_⟩
  refine torsion_basis_of_generization A₁ M (h + h) (fun i => lv₁ (toStd (Pi.single i 1))) hA hM hu'
    (fun i => lv_pow hadd _) (fun p => ?_) k x y hy
  obtain ⟨K, _, _, z, hz⟩ := exists_geomPt_specializes R R₁ p
  exact ⟨K, inferInstance, inferInstance, z ≫ spMap R₁.subtype, hz,
    (cond_iff hadd _).1 (cond_push hp hl z (hlev.2 K z))⟩

end GlobalTheory.LevelDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamily
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNormU

theorem germ_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens)
    (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  apply Units.ext
  rw [gm_val (r ≫ q) z U h]
  show _ = (r.stalkMap z).hom (gm q (r z) U a).val
  rw [gm_val q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ U) z h _).symm

variable {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B]

theorem zb_zb : zb A B ≫ zb A B = zb A B := by ext <;> simp [zb]
theorem zb_fst' : zb A B ≫ fst A B = fst A B := by simp [zb]
theorem fst_comp_lift_id_one_eq_prodSetSecondCoordZero : fst A B ≫ lift (𝟙 A) (1 : A ⟶ B) = zb A B := by ext <;> simp [zb]

theorem rhoZ_rhoZ (q : A ⟶ A') : rhoZ (B := B) q ≫ rhoZ q = rhoZ q := by
  have e : (zb A B).left ≫ (zb A B).left = (zb A B).left := by rw [← Over.comp_left, zb_zb]
  apply pullback.hom_ext <;> simp [e]

theorem rhoZ_a (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_fst_assoc, ← Over.comp_left, zb_fst']

theorem rhoZ_a' (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_snd_assoc, ← Over.comp_left, zb_fst']

theorem a_s (q : A ⟶ A') : (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_fst, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

theorem pullbackSnd_fst_comp_lift_id_one (q : A ⟶ A') : (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_snd, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem germ_gen {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (τ : LB.Gen (L.pull F)) (hτ : τ.IsGen)
    (g : Y ⟶ X') (y : Y) (i i' : L.ι) (hi : F (g y) ∈ L.U i) (hi' : F (g y) ∈ L.U i') :
    gm g y _ (τ.s fun _ => i) = gm (g ≫ F) y _ (L.g i i') * gm g y _ (τ.s fun _ => i') := by
  have hp : g y ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  have e : gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i')) ((L.pull F).g (fun _ => i) (fun _ => i')) =
      gm (g ≫ F) y _ (L.g i i') := by
    show gm g y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g i i'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res g y _ hp _).trans (gm_pull g F y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _)
  have := congrArg (gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i'))) (hτ (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res g y _ hp, gm_res g y _ hp, e] at this
  exact this

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem pt_eq {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← e]; rfl

theorem rhoZ_rhoZ_apply {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B] (q : A ⟶ A') (z) :
    rhoZ (B := B) q (rhoZ q z) = rhoZ q z := pt_eq (rhoZ_rhoZ q) z

set_option maxHeartbeats 800000 in

theorem normalise : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → τ.IsGen → ∀ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ, DescCompat (q ▷ B).left P φ → ∃ u : Γ(pullback (q ▷ B).left (q ▷ B).left, ⊤)ˣ, NormAlong q P τ (GlobalTheory.DescNorm.twist (q ▷ B).left P φ u) := by
  intro K _ A A' B _ _ q P τ hP hτ φ hφ
  let W : P.ι × P.ι → (pullback (q ▷ B).left (q ▷ B).left).Opens := fun p => rhoZ q ⁻¹ᵁ chart (q ▷ B).left P p.1 p.2
  have h2 : ∀ p, W p ≤ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.1) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (a_s q) z]; exact hz.1)
  have h3 : ∀ p, W p ≤ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.2) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz.2)
  let v : ∀ p, Γ(pullback (q ▷ B).left (q ▷ B).left, W p)ˣ := fun p =>
    (pullU (rhoZ q) _ (φ p.1 p.2))⁻¹ *
      (res (h2 p) (pullU (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.1)))⁻¹ *
      res (h3 p) (pullU (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.2))
  have hv : ∀ (Y : Scheme.{0}) (g : Y ⟶ pullback (q ▷ B).left (q ▷ B).left) (y : Y) (p : P.ι × P.ι), g y ∈ W p →
      gm g y (W p) (v p) = (gm (g ≫ rhoZ q) y _ (φ p.1 p.2))⁻¹ *
        (gm (g ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.1))⁻¹ *
        gm (g ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.2) := by
    intro Y g y p hy
    simp only [v, map_mul, map_inv]
    rw [gm_pull g (rhoZ q) y _ hy, gm_res g y (h2 p) hy, gm_pull g (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h2 p hy),
      gm_res g y (h3 p) hy, gm_pull g (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h3 p hy)]

  have indep : ∀ p p', ∀ z ∈ W p ⊓ W p', gm (𝟙 _) z (W p) (v p) = gm (𝟙 _) z (W p') (v p') := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hz, hz'⟩
    rw [hv _ (𝟙 _) z _ hz, hv _ (𝟙 _) z _ hz']
    simp only [Category.id_comp]
    have hz1 : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i := hz.1
    have hz2 : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j := hz.2
    have hz1' : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i' := hz'.1
    have hz2' : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j' := hz'.2
    have c1 : gm (rhoZ q) z _ (φ i' j') = gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') *
        gm (rhoZ q) z _ (φ i j) * gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) := by
      have e := congrArg (Units.map ((rhoZ q).stalkMap z).hom.toMonoidHom) (hφ (rhoZ q z) i i' j j' hz1 hz1' hz2 hz2')
      rw [map_mul, map_mul] at e
      have k1 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i' j') ⟨hz1', hz2'⟩ (φ i' j')
      have k2 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i j) ⟨hz1, hz2⟩ (φ i j)
      have k3 := germ_comp (rhoZ q) (pullback.fst (q ▷ B).left (q ▷ B).left) z (P.U i ⊓ P.U i') ⟨hz1, hz1'⟩ (P.g i i')
      have k4 := germ_comp (rhoZ q) (pullback.snd (q ▷ B).left (q ▷ B).left) z (P.U j' ⊓ P.U j) ⟨hz2', hz2⟩ (P.g j' j)
      rw [Category.comp_id] at k1 k2
      rw [k1, k2, k3, k4]
      exact e
    have t1 := germ_gen τ hτ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z i i'
      (by rw [pt_eq (a_s q) z]; exact hz1) (by rw [pt_eq (a_s q) z]; exact hz1')
    have t2 := germ_gen τ hτ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z j j'
      (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2) (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2')
    rw [a_s] at t1
    rw [pullbackSnd_fst_comp_lift_id_one] at t2
    have cc := gm_cocycle hP (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z hz2 hz2' hz2
    rw [gm_self hP _ z hz2] at cc
    rw [c1, t1, t2]
    generalize gm (rhoZ q) z _ (φ i j) = Φ
    generalize gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') = G₁
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) = G₂ at cc ⊢
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j j') = H at cc ⊢
    generalize gm (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => i') = T₁
    generalize gm (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => j') = T₂
    rw [eq_inv_of_mul_eq_one_left cc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hc : (⊤ : (pullback (q ▷ B).left (q ▷ B).left).Opens) ≤ iSup W := fun z _ => by
    obtain ⟨i, hi⟩ := exists_chart hP (pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z))
    obtain ⟨j, hj⟩ := exists_chart hP (pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) hc v indep
  refine ⟨u, fun T r t i j hi hj => ?_⟩
  have hm : (r ≫ rhoZ q) t ∈ chart (q ▷ B).left P i j := ⟨hi, hj⟩
  have hw : (r ≫ rhoZ q) t ∈ W (i, j) := by
    show rhoZ q (rhoZ q (r t)) ∈ chart (q ▷ B).left P i j
    rw [rhoZ_rhoZ_apply]; exact hm
  show gm _ t _ (φ i j * res le_top u) = _
  rw [map_mul, gm_res _ t le_top hm, ← gm_res _ t (le_top : W (i, j) ≤ ⊤) hw u, hu (i, j), hv T (r ≫ rhoZ q) t (i, j) hw]
  simp only [Category.assoc, rhoZ_rhoZ, rhoZ_a, rhoZ_a']
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]

end GlobalTheory.DescNormU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueMorphismsIntegralAgreeAtGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) → ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P), (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) → ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  first | exact @GlobalTheory.Desc.GenGlue.exists_glue | exact GlobalTheory.Desc.GenGlue.exists_glue | (intros; apply GlobalTheory.Desc.GenGlue.exists_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompletionChartToExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_completionChart_to_extension : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  first | exact @GlobalTheory.Desc.exists_grpPullback_chart_to_ext | exact GlobalTheory.Desc.exists_grpPullback_chart_to_ext | (intros; apply GlobalTheory.Desc.exists_grpPullback_chart_to_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetweenStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonicPolynomial_localDepth_between : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  first | exact @GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | exact GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | (intros; apply GlobalTheory.RefSum.GlobalPoly.exists_polyBetween <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarCuspFormIndefiniteUnitaryShimuraStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_cuspForm_indefinite_unitaryShimura : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → 1 ≤ Dw.p → 1 ≤ Dw.q → ¬ (∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)) → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  first | exact @GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite | exact GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite | (intros; apply GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite <;> assumption)
end

