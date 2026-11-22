import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0747
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0675
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSections
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.ApproxCorr

theorem map_mem_pow {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    {n : ℕ} {a : A} (h : a ∈ maximalIdeal A ^ n) : φ a ∈ maximalIdeal B ^ n := by
  have h1 := Ideal.mem_map_of_mem φ h
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le φ) n h1

theorem mem_of_forall_mem_sup {C : Type} [CommRing C] [IsLocalRing C] [IsNoetherianRing C] (I : Ideal C) (c : C)
    (h : ∀ n : ℕ, c ∈ I ⊔ maximalIdeal C ^ n) : c ∈ I := by
  have k := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C ⧸ I) (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top
  have : Submodule.mkQ I c ∈ (⊥ : Submodule C (C ⧸ I)) := by
    rw [← k, Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h n)
    have e : Submodule.mkQ I (a + b) = b • Submodule.mkQ I 1 := by
      rw [map_add, ← map_smul, smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero I).2 ha |> (Submodule.mkQ_apply I a).trans,
        zero_add]
    rw [e]
    exact Submodule.smul_mem_smul hb trivial
  exact (Submodule.Quotient.mk_eq_zero I).1 ((Submodule.mem_bot C).1 this)

theorem exists_stalk_map {Z S : Scheme.{0}} (π : S ⟶ Z) (x : S) (z : Z) (h : π x = z) :
    ∃ ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x, IsLocalHom ψ ∧
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π := by
  subst h
  exact ⟨(π.stalkMap x).hom, π.toLRSHom.prop x, Scheme.SpecMap_stalkMap_fromSpecStalk π⟩

theorem mem_map_of_approx {Z S : Scheme.{0}} (π : S ⟶ Z) [IsProper π] (I : S.IdealSheafData) (z : Z)
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (i : Z.presheaf.stalk z →+* R) [IsLocalHom i] (hi : i.Flat)
    (F : R) (a : ℕ → Z.presheaf.stalk z) (ha : ∀ n, F - i (a n) ∈ maximalIdeal R ^ n)
    (H : ∀ (x : S) (ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x), IsLocalHom ψ →
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π → ∀ n, ψ (a n) ∈ FinalTheorems.stalkId I x ⊔ maximalIdeal _ ^ n) :
    F ∈ (FinalTheorems.stalkId (I.map π) z).map i := by
  rw [← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]
  generalize hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ
  have hfl : Flat ξ := by
    rw [← hξ]
    haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z
    haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi
    infer_instance
  have hξc : ξ (closedPoint R) = z := by
    rw [← hξ]
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  refine GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_
  · rw [Scheme.stalkClosedPointTo, CommRingCat.hom_comp]
    exact RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
  refine GlobalTheory.T.germ_mem_idealSheaf_stalk_of_closedFibre_univClosed _ R (Limits.pullback.fst ξ π) _ _ fun v hv => ?_
  haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)
  set p := Limits.pullback.fst ξ π with hp
  set q := Limits.pullback.snd ξ π with hq
  have hpq : p ≫ ξ = q ≫ π := Limits.pullback.condition
  have hx : π (q v) = z := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]
  obtain ⟨ψ, hψ, hψc⟩ := exists_stalk_map π (q v) z hx
  let α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v
  have hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p := by
    rw [Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  haveI : IsLocalHom α.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_
    change Spec.map α (closedPoint _) = _
    rw [hα]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)
  haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v
  have hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v := by
    refine Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)
    rw [Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]
    erw [hψc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  have hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t) := fun t => congrArg (fun f => f.hom t) hc
  have e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F :=
    (Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm
  rw [e]
  refine mem_of_forall_mem_sup _ _ fun n => ?_
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 (H (q v) ψ hψ hψc n)
  have e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a n))) := by
    rw [← add_assoc, ← map_add, hbc, ← hc', map_sub]; ring
  rw [e2]
  exact Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb))
    (add_mem (map_mem_pow _ hc) (map_mem_pow _ (ha n)))

theorem charZero_essFiniteType {S : Scheme.{0}} (s : S ⟶ Sp ℤ) [Flat s] [LocallyOfFiniteType s] (x : S) :
    CharZero (S.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (S.presheaf.stalk x) := by
  let y : PrimeSpectrum ℤ := s x
  letI A : Algebra ℤ ((Sp ℤ).presheaf.stalk (s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime ℤ _ ((Sp ℤ).presheaf.stalk (s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap ℤ ((Sp ℤ).presheaf.stalk (s x)) _ _ A
  have h₁ : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp ℤ).presheaf.stalk (s x)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsLocalHom (s.stalkMap x).hom := s.toLRSHom.prop x
  have hσ : Function.Injective (s.stalkMap x).hom := by
    have h := Flat.stalkMap s x
    algebraize [(s.stalkMap x).hom]
    have : IsLocalHom (algebraMap ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)) := this
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp ℤ).presheaf.stalk (s x)) (B := S.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)
  refine ⟨charZero_of_injective_ringHom (f := (s.stalkMap x).hom.comp φ) (hσ.comp hφ), ?_⟩
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert h₂.comp h₁ using 1
  exact Subsingleton.elim _ _

theorem range_subset {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : (U : Set S).Nonempty) (x : S)
    {V : Type} [CommRing V] [IsDomain V] (ρ : S.presheaf.stalk x →+* V) (hρ : Function.Injective ρ) :
    Set.range (jK V ≫ spMap ρ ≫ S.fromSpecStalk x) ⊆ U := by
  rintro _ ⟨t, rfl⟩
  have hg : genericPoint S ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
  obtain ⟨w, hw⟩ := hg
  have ht : (jK V ≫ spMap ρ) t ⤳ w := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h0 : algebraMap V (FractionRing V) (ρ r) ∈ t.asIdeal := hr
    have h1 : algebraMap V (FractionRing V) (ρ r) = 0 := by
      by_contra hne
      exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 (Ne.isUnit hne))
    have h2 : r = 0 := hρ (by rw [map_zero]; exact IsFractionRing.injective V (FractionRing V) (by rw [h1, map_zero]))
    rw [h2]; exact zero_mem _
  have h3 := ht.map (S.fromSpecStalk x).continuous
  rw [← Category.assoc, Scheme.Hom.comp_apply]
  have h4 : S.fromSpecStalk x ((jK V ≫ spMap ρ) t) = genericPoint S :=
    ((show _ ⤳ genericPoint S from hw ▸ h3).antisymm (genericPoint_specializes _)).eq
  rw [h4]
  exact ((genericPoint_spec S).mem_open_set_iff U.2).2 (by simpa using hU)

theorem exists_correction : ∀ (Z S : Scheme.{0}) [IsIntegral Z] [IsIntegral S] (sZ : Z ⟶ Sp ℤ) [LocallyOfFiniteType sZ] [QuasiCompact sZ] (π : S ⟶ Z) [IsProper π] [IsDominant π] [Flat (π ≫ sZ)], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (E : GlobalTheory.EffCartierData S) (z : Z) (k : ℕ), ∃ e : ℕ, ∀ f : Z.presheaf.stalk z, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev → spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U → ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e) → f ∈ FinalTheorems.stalkId (E.idealSheaf.map π) z ⊔ maximalIdeal _ ^ k := by
  intro Z S _ _ sZ _ _ π _ _ _ hS U hU E z k
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let K : ℕ → Ideal (Z.presheaf.stalk z) := fun e =>
    { carrier := {f | ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev →
        spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U →
        ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e}
      add_mem' := fun ha hb V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [map_add]; exact add_mem (ha V hV ξ ev h1 h2 h3) (hb V hV ξ ev h1 h2 h3)
      zero_mem' := fun V _ _ _ _ hV ξ ev h1 h2 h3 => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun c a ha V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ (ha V hV ξ ev h1 h2 h3) }
  refine GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone (Z.presheaf.stalk z) K (FinalTheorems.stalkId (E.idealSheaf.map π) z) ?_ ?_ ?_ k
  · intro m n hmn f hf V _ _ _ _ hV ξ ev h1 h2 h3
    exact (show _ ≤ (_ : Ideal V) from sup_le_sup_left (Ideal.pow_le_pow_right hmn) _) (hf V hV ξ ev h1 h2 h3)
  · intro e f hf V _ _ _ _ hV ξ ev h1 h2 h3
    refine Ideal.mem_sup_right ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf
  intro F a ha hK
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (Z.presheaf.stalk z))
  haveI : Module.FaithfullyFlat (Z.presheaf.stalk z) (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine mem_map_of_approx π E.idealSheaf z _ (RingHom.flat_algebraMap_iff.2 inferInstance) F a ha fun x ψ hψ hc => ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ E.U i := TopologicalSpace.Opens.mem_iSup.1 (E.cover ▸ trivial)
  obtain ⟨h0, hft⟩ := charZero_essFiniteType (π ≫ sZ) x
  haveI := (hS x).2
  have hI := E.stalkId_idealSheaf i x hi
  rw [hI]
  refine GlobalTheory.T.mem_span_sup_pow_of_forall_complete_dvr_local_test (S.presheaf.stalk x) _ (fun n => ψ (a n))
    (nonZeroDivisors.ne_zero (GlobalTheory.Cartier.isRegularFn_iff_germ.1 (E.regular i) x hi)) ?_ ?_
  · intro m n hmn
    rw [← map_sub]
    refine map_mem_pow ψ ?_
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
      (maximalIdeal (Z.presheaf.stalk z) ^ m), Ideal.mem_comap, Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map, map_sub]
    have := sub_mem (Ideal.pow_le_pow_right hmn (ha n)) (ha m)
    rwa [sub_sub_sub_cancel_left] at this
  · intro V _ _ _ _ hV ρ hρ hl e
    have hl' : IsLocalHom (ρ.comp ψ) := inferInstance
    have h1 := hK e V hV (spMap ρ ≫ S.fromSpecStalk x) (ρ.comp ψ) hl' (by
      rw [Category.assoc, ← hc, ← Category.assoc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]) (range_subset U hU x ρ hρ)
    rw [GlobalTheory.PolDiv.idlAlong_fromSpecStalk, hI, Ideal.map_span, Set.image_singleton] at h1
    exact (show _ ≤ (_ : Ideal V) from
      sup_le_sup_left (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (ρ.comp ψ)) e) _) h1

end GlobalTheory.ApproxCorr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpDescent
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CPDesc

theorem cancel_of_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Surjective π]
    (h : ∀ W, Function.Injective (π.app W)) {Z : Scheme.{0}} (a b : Y ⟶ Z) (hab : π ≫ a = π ≫ b) : a = b := by
  have hb : a.base = b.base := by
    ext y
    obtain ⟨x, rfl⟩ := π.surjective y
    exact congr($hab x)
  refine Scheme.Hom.ext hb fun U ↦ ?_
  have : Mono (π.app (b ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (h _)
  rw [← cancel_mono (π.app _)]
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, hab]

end GlobalTheory.Mum.CPDesc

namespace GlobalTheory.Mum
open CPDesc

theorem flat_tensor {S : Scheme.{0}} (G H : Over S) [Flat G.hom] [Flat H.hom] : Flat (G ⊗ H).hom := by
  show Flat (pullback.fst G.hom H.hom ≫ G.hom); infer_instance

theorem exists_cp_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G')
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G →
    IsGrpPullback G' G M.π β → ∀ L : LB G.left, L.IsLB → LBIso P'.L.L (L.pull β) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG h L hL hLw
  obtain ⟨w, hw⟩ := hLw
  obtain ⟨_, -, _, -⟩ := hR
  have hp := (isGen_iff w).1 hw
  obtain ⟨hbijπ, hsurjπ⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  have := M.proper
  have hf1 : Flat G.hom := by have := hG.smooth; infer_instance
  have hf2 : Flat (G2 G).hom := flat_tensor _ _
  have hf3 : Flat (G3 G).hom := by have := hf2; exact flat_tensor _ _
  have hf4 : Flat (G4 G).hom := by have := hf3; exact flat_tensor _ _
  have key : ∀ {Y Z : Scheme.{0}} (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ M.S), Flat y → IsPullback p q y M.π →
      (∀ V, Function.Bijective (p.app V).hom) ∧ (∀ {X : Scheme.{0}} (a b : Y ⟶ X), p ≫ a = p ≫ b → a = b) := by
    intro Y Z y p q hy hpb
    have hb := GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R M.S Y Z M.π y p q inferInstance inferInstance hbijπ hy hpb
    have : Surjective p := MorphismProperty.of_isPullback hpb.flip hsurjπ
    exact ⟨hb, fun a b e => cancel_of_surjective p (fun V => (hb V).1) a b e⟩
  obtain ⟨A2, A3, A4⟩ := GlobalTheory.T.isPullback_powers_cartesian_group_square h
  have k0 := key (𝟙 (Sp R)) M.π (𝟙 M.S) inferInstance (IsPullback.id_vert M.π)
  have k1 := key G.hom β G'.hom hf1 h.1
  have k2 := key _ _ _ hf2 A2
  have k3 := key _ _ _ hf3 A3
  have k4 := key _ _ _ hf4 A4

  obtain ⟨rig, hr, -⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB M.π k0.1 (K := PUnit) (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (fun _ => (cubeMapOf h).e_comm) P'.L.rig P'.L.rigGen

  have hι : (ι[G']).left ≫ β = β ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ β) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ β = β ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s, hs, vs⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB β k1.1 hc₂ P'.sym P'.sym_gen

  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ β = (cubeMapOf h).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf h).psum_comm I.down
  obtain ⟨t, ht, vt⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB (cubeMapOf h).F3 k3.1 hc P'.c.t P'.c.isGen
  let L₁ : RigLB G := ⟨L, rig, hL, hr⟩
  let Wf : ∀ {T : Over M.S} (z : T.left), ((T.left ⟶ G.left) → L.ι) → ((T.left ⟶ G'.left) → P'.L.L.ι) →
      (T ⟶ G') → (T.left.presheaf.stalk z)ˣ := fun z I J x => gw w x.left z (I (x.left ≫ β)) (J x.left)
  have vcub : ∀ (T : Over M.S) (z : T.left) (I J), Good L z I → Good P'.L.L z J → ∀ a b d : T ⟶ G',
      GlobalTheory.CubTransport.thV (L := L₁) t z I (pushHom h T a) (pushHom h T b) (pushHom h T d) =
        Wf z I J (a * b * d) * (Wf z I J (a * b))⁻¹ * (Wf z I J (a * d))⁻¹ * (Wf z I J (b * d))⁻¹ * Wf z I J a *
          Wf z I J b * Wf z I J d * (Wf z I J 1)⁻¹ * cubV P'.c z J a b d := by
    intro T z I J hI hJ a b d
    have q : (lift a (lift b d)).left ≫ (cubeMapOf h).F3 =
        (lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := vt _ (lift a (lift b d)).left z I J hI hJ
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw w q z (I (q ≫ β)) (J q))) rfl)
  have vsym : ∀ (T : Over M.S) (z : T.left) (I J), Good L z I → Good P'.L.L z J → ∀ a : T ⟶ G',
      val s (pushHom h T a).left z I = Wf z I J a⁻¹ * (Wf z I J a)⁻¹ * val P'.sym a.left z J := by
    intro T z I J hI hJ a
    exact (vs _ a.left z I J hI hJ).trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.prod_sym a (fun q => gw w q z (I (q ≫ β)) (J q))) rfl)
  obtain ⟨c, hct⟩ := GlobalTheory.T.cubicalStructure_of_pushed_point_values_cube_function h L₁ t ht (fun U => (k2.1 U).1) k2.2 (fun U => (k3.1 U).1) k3.2
    (fun U => (k4.1 U).1) k4.2 fun T z I hI => by
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
      refine GlobalTheory.CubTransport.isCub_of_twist (isCub_cubV P'.c hJ) (MonoidHom.id _) (fun a => (Wf z I J a)⁻¹)
        fun a b d => ?_
      rw [MonoidHom.id_apply, MonoidHom.id_apply, MonoidHom.id_apply, vcub T z I J hI hJ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
  subst hct
  have symCub := GlobalTheory.T.cubeSymm_compat_descends_from_pushed_points h L₁ c s hs (fun U => (k3.1 U).1) k3.2 fun T z I hI x y u => by
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
    refine GlobalTheory.UU.sym_cub_alg (MonoidHom.id _) (fun a => (Wf z I J a)⁻¹) (θ := cubV P'.c z J)
      (θ' := fun a b d => cubV c z I (pushHom h T a) (pushHom h T b) (pushHom h T d))
      (σ := fun a => val P'.sym a.left z J) (σ' := fun a => val s (pushHom h T a).left z I) (fun a b d => ?_)
      (fun a => ?_) (P'.sym_cub T x y u z J hJ)
    · have := vcub T z I J hI hJ a b d
      show cubV P'.c z J a b d = _
      rw [show cubV c z I (pushHom h T a) (pushHom h T b) (pushHom h T d) =
        GlobalTheory.CubTransport.thV (L := L₁) c.t z I (pushHom h T a) (pushHom h T b) (pushHom h T d) from rfl, this]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
    · show val P'.sym a.left z J = _
      rw [vsym T z I J hI hJ a]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
  have symRig : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s (eSec G)) (LB.oneGen L₁.L) := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull hL M.π (fun U => (k0.1 U).1) (fun a b e => k0.2 a b e)
      fun z I hI => ?_
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
    have e₁ : M.π ≫ eSec G = eSec G' ≫ β := (cubeMapOf h).e_comm.symm
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    have e₃ := vs _ (eSec G') z I J hI hJ
    have e₄ : val P'.sym (eSec G') z J = 1 := by
      have := (val_pull hJ P'.sym (eSec G') (𝟙 _)).symm.trans ((val_corr hJ P'.sym_rig (𝟙 _)).trans (val_one _))
      rwa [Category.id_comp] at this
    rw [val_pull hI, e₁, e₃, e₄, Fin.prod_univ_two, val_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul]
  exact ⟨⟨L₁, c, s, hs, symRig, fun T x y u z J hJ => symCub T x y u z J hJ⟩, rfl⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrossRelationSectionsAmpleSourcePower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

open GlobalTheory.PullPair LBGerm GlobalTheory.AbLaw

def chartPullTwJ {X₁ X₂ : Scheme.{0}} (M₁ : LB X₁) (M₂ : LB X₂) (f : X₁ ⟶ X₂) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t) (𝟙 X₁) where
  idx J := (fun _ => J 0, fun _ => (J 1).1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0,
    Set.mem_iInter.2 fun _ => ((isPart_inl M₁ M₂).mem _ _).1 (Set.mem_iInter.1 hy 1)⟩
  g y J J' hJ hJ' := by
    have P := isPart_inl M₁ M₂
    have a₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ 1)
    have b₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J' 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ' 1)
    have hg := P.g _ (𝟙 X₁) y (J 1) (J' 1) ((P.mem _ _).1 (Set.mem_iInter.1 hJ 1)) ((P.mem _ _).1 (Set.mem_iInter.1 hJ' 1))
    refine (gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t y
      (fun _ => J 0, fun _ => (J 1).1) (fun _ => J' 0, fun _ => (J' 1).1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X₁) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb _ _ _ (𝟙 X₁) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp] at hg ⊢
    rw [hg]

theorem exists_sec_twist_join {X₁ X₂ : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} (h : IsAmpleLB M₁) (h₂ : M₂.IsLB)
    [Nonempty X₁] [Nonempty X₂] (f : X₁ ⟶ X₂) (e : ℤ) (k : ℕ) (hk : 1 ≤ k) (y : X₁) :
    ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  have hN := join_isLB hL h₂
  obtain ⟨m, hm, s, hs, -, ha⟩ := h.exists_affine_le (x := y) (U := ⊤) trivial
  obtain ⟨V, N, hV, H⟩ := TwistGen.exists_nhds
    (M := LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e))
    (LB.isLB_linComb hN _ _) (isLB_lbPow hL m) s ha y hs
  obtain ⟨d, hd⟩ : ∃ d, k * (N + 1) = N + d := Nat.exists_eq_add_of_le (by nlinarith)
  obtain ⟨u, hu⟩ := H d
  refine ⟨m * (N + 1), Nat.mul_pos hm (Nat.succ_pos N), ?_⟩
  rw [show k * (m * (N + 1)) = m * (N + d) by rw [← hd]; ring]
  refine ⟨chartSec (chartPullTwJ M₁ M₂ f e m (N + d)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id _ u fun x _ _ => exists_chart (LB.isLB_linComb hN _ _) x]
  exact hu hV

theorem exists_crossH : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧
      ∀ t₁ t₂ : SecA A₂ F j, ∃ t₁' t₂' : SecA A₁ F (k * n), CrossH c t₁ t₂ t₁' t₂' ∧
        ((∀ z J, Good A₂.L z J → sA t₂ (ptSecT A₂.A 1).left z J ≠ 0) →
          (∀ z J, Good A₁.L z J → sA t₂' (ptSecT A₁.A 1).left z J ≠ 0)) := by
  intro R _ _ A₁ A₂ F _ _ c hc j k hk
  have hL₁ := A₁.isLB
  have hL₂ := A₂.isLB
  let T : Over (Sp (FractionRing R)) := TFK (R := R) F
  have hsub : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let z₀ : T.left := (⊥ : PrimeSpectrum F)
  have P₁ := isPart_inl A₁.L A₂.L
  have P₂ := isPart_inr A₁.L A₂.L
  have hN := join_isLB hL₁ hL₂
  obtain ⟨n, hn, u, hu⟩ := exists_sec_twist_join (isAmpleLB_of_relAmple_of_isAffine A₁.A hL₁ A₁.ample) hL₂ c.left
    (-(j : ℤ)) k hk (((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀)
  have key : ∀ t : SecA A₂ F j, ∃ t' : SecA A₁ F (k * n), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A₁.A).left) (z : Z) (J),
      Good (join A₁.L A₂.L) z J →
        sA t' r z (rl J) = sA t (r ≫ (T ◁ c).left) z (rr J) * sval u (r ≫ (snd T A₁.A).left) z J := by
    intro t
    have e : (T ◁ c).left ≫ (snd T A₂.A).left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) =
        (snd T A₁.A).left ≫ c.left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) := by
      rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
    let tN := P₂.sec (φ := fun _ : Fin 1 => (snd T A₂.A).left) (ε := fun _ => (j : ℤ)) t
    obtain ⟨s, hs⟩ := exists_sec hN (φ' := fun _ : Fin 1 => (snd T A₁.A).left ≫ coprod.inl)
      (ε' := fun _ => ((k * n : ℕ) : ℤ))
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
          Matrix.cons_val_zero, Matrix.cons_val_one, e, zpow_neg, mul_inv_cancel_left])
      (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec tN (T ◁ c).left) (H1.SectionArithmetic.pullSec u (snd T A₁.A).left))
    obtain ⟨t', ht'⟩ := P₁.exists_sec (φ := fun _ : Fin 1 => (snd T A₁.A).left) (ε := fun _ => ((k * n : ℕ) : ℤ)) hL₁
      (fst_surjective hL₂) s
    refine ⟨t', fun Z r z J hJ => (ht' Z r z J hJ).trans ((hs Z r z J hJ).trans ?_)⟩
    refine (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) ?_ (H1.SectionArithmetic.sval_pullSec _ _ r z hJ))
    exact (H1.SectionArithmetic.sval_pullSec _ _ r z hJ).trans (P₂.sval_sec _ _ z hJ)
  refine ⟨n, hn, fun t₁ t₂ => ?_⟩
  obtain ⟨t₁', h₁⟩ := key t₁
  obtain ⟨t₂', h₂⟩ := key t₂
  refine ⟨t₁', t₂', fun z J₁ J₂ g₁ g₂ => ?_, fun h z J₁ g₁ => ?_⟩
  · obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join hL₁ hL₂ g₁ g₂
    rw [h₁ _ _ z J hJ, h₂ _ _ z J hJ, Category.id_comp]
    ring
  · choose d hd using fun ψ : T.left ⟶ A₂.A.left => exists_chart hL₂ (ψ z)
    obtain ⟨J, hJ, rfl, hr⟩ := exists_good_join hL₁ hL₂ g₁ (J₂ := d) hd
    have e : (ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (T ◁ c).left = (ptSecT A₂.A (1 : T ⟶ A₂.A)).left := by
      rw [← Over.comp_left, ptSecT, ptSecT, lift_whiskerLeft, MonObj.one_comp]
    rw [h₂ _ _ z J hJ, e]
    obtain rfl : z₀ = z := Subsingleton.elim _ _
    have hU : IsUnit (sval u ((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀ J) :=
      (mem_nonzeroLocus_iff_pull u _ z₀ (hJ.mem _ _)).1 hu
    have g₂ : Good A₂.L z₀ (rr J) := hr ▸ hd
    exact fun h0 => h z₀ (rr J) g₂ (hU.mul_left_eq_zero.1 h0)

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubeStep_generator_tensorPowerPairs : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  first | exact @GlobalTheory.Mum.cube_step | exact GlobalTheory.Mum.cube_step | (intros; apply GlobalTheory.Mum.cube_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspRuleOfBoundaryVanishingComponentSectioStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  first | exact @GlobalTheory.OrbitSep.exists_rule_of_cls_pull | exact GlobalTheory.OrbitSep.exists_rule_of_cls_pull | (intros; apply GlobalTheory.OrbitSep.exists_rule_of_cls_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC) (π : C →ₐ[R] B) (w : C →+ K1 R δ), (∀ x y, w (x * y) = π x • w y + π y • w x) → (∀ r, w (algebraMap R C r) = 0) → (∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) → ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧ (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧ (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧ (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  first | exact @GlobalTheory.PDForm.exists_lift_of_pdDerivation | exact GlobalTheory.PDForm.exists_lift_of_pdDerivation | (intros; apply GlobalTheory.PDForm.exists_lift_of_pdDerivation <;> assumption)
end

