import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCommMonObjTors
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0025
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionAppLESurjectiveAndKer
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.MuConst GlobalTheory.HTSheaf GlobalTheory.LieVB
open GlobalTheory.Conormal

namespace GlobalTheory.TorsionChart

theorem pushout_inl_surjective_and_ker {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ D} {j : C ⟶ D} (po : IsPushout f g i j) (hg : Function.Surjective g.hom) :
    Function.Surjective i.hom ∧ RingHom.ker i.hom = Ideal.map f.hom (RingHom.ker g.hom) := by
  set I := Ideal.map f.hom (RingHom.ker g.hom) with hIdef
  have hw : ∀ a, i.hom (f.hom a) = j.hom (g.hom a) := fun a => congr($(po.w).hom a)
  have hI : I ≤ RingHom.ker i.hom := by
    rw [hIdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hw, (RingHom.mem_ker).1 ha, map_zero]
  let mk : B ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hker : RingHom.ker g.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp f.hom) := by
    intro a ha
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : {g' : A →+* B ⧸ I // RingHom.ker g.hom ≤ RingHom.ker g'} :=
    ⟨(Ideal.Quotient.mk I).comp f.hom, hker⟩
  let ψ : C ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (g.hom.liftOfSurjective hg φ)
  have hψ : f ≫ mk = g ≫ ψ := by
    ext a
    exact (RingHom.liftOfSurjective_comp_apply g.hom hg φ a).symm
  let lift : CommRingCat.of (B ⧸ I) ⟶ D := CommRingCat.ofHom (Ideal.Quotient.lift I i.hom hI)
  have h1 : i ≫ po.desc mk ψ hψ = mk := po.inl_desc _ _ _
  have h2 : po.desc mk ψ hψ ≫ lift = 𝟙 D := by
    refine po.hom_ext ?_ ?_
    · rw [← Category.assoc, h1, Category.comp_id]
      ext b
      rfl
    · rw [← Category.assoc, po.inr_desc, Category.comp_id]
      ext c
      obtain ⟨a, rfl⟩ := hg c
      change lift.hom (ψ.hom (g.hom a)) = j.hom (g.hom a)
      rw [show ψ.hom (g.hom a) = mk.hom (f.hom a) from
        (RingHom.liftOfSurjective_comp_apply g.hom hg φ a), ← hw]
      rfl
  refine ⟨fun d => ?_, le_antisymm (fun b hb => ?_) hI⟩
  · obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((po.desc mk ψ hψ).hom d)
    refine ⟨b, ?_⟩
    have := congr($(h2).hom d)
    change lift.hom ((po.desc mk ψ hψ).hom d) = d at this
    rw [← hb] at this
    exact this
  · have := congr($(h1).hom b)
    change (po.desc mk ψ hψ).hom (i.hom b) = Ideal.Quotient.mk I b at this
    rw [(RingHom.mem_ker).1 hb, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

end GlobalTheory.TorsionChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsCharExt

theorem exists_hom_extend {G A : Type} [CommGroup G] [CommGroup A]
    (hA : ∀ n : ℕ, n ≠ 0 → ∀ a : A, ∃ b : A, b ^ n = a) (q : ℕ) (χ : G → A)
    (hχ : ∀ g g', g ^ q = 1 → g' ^ q = 1 → χ (g * g') = χ g * χ g') :
    ∃ κ : G →* A, ∀ g, g ^ q = 1 → κ g = χ g := by
  let T : Subgroup G := (powMonoidHom q : G →* G).ker
  let f : T →* A := MonoidHom.mk' (fun g => χ g) fun g g' => hχ g g' g.2 g'.2
  letI : DivisibleBy (Additive A) ℕ := divisibleByOfSMulRightSurj (Additive A) ℕ fun {n} hn a => by
    obtain ⟨b, hb⟩ := hA n hn a.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  letI : DivisibleBy (Additive A) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨k, hk⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive T.subtype) (fun a b h => Subtype.ext h) (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm k, fun g hg => ?_⟩
  exact DFunLike.congr_fun hk (Additive.ofMul (⟨g, hg⟩ : T))

section Ring

variable (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]

def intV : ValuationSubring C where
  toSubring := intO C
  mem_or_inv_mem' := fun x => by
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      change ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

theorem intO_valuationRing : ValuationRing ↥(intO C) := inferInstanceAs (ValuationRing ↥(intV C))

theorem intO_isFractionRing : IsFractionRing ↥(intO C) C := inferInstanceAs (IsFractionRing ↥(intV C) C)

theorem intO_units_root [IsAlgClosed C] (n : ℕ) (hn : n ≠ 0) (a : (↥(intO C))ˣ) : ∃ b : (↥(intO C))ˣ, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ↥(intO C)) : C) (Nat.pos_of_ne_zero hn)
  have h1 : ‖z‖ ≤ 1 := by
    have h : ‖((a : ↥(intO C)) : C)‖ ≤ 1 := (a : ↥(intO C)).2
    rw [← hz, norm_pow] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hn).1 h
  have h2 : (⟨z, h1⟩ : ↥(intO C)) ^ n = a := Subtype.ext hz
  have h3 : IsUnit (⟨z, h1⟩ : ↥(intO C)) := (isUnit_pow_iff hn).1 (h2 ▸ a.isUnit)
  exact ⟨h3.unit, Units.ext h2⟩

end Ring

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def pull {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a') :
    (Over.mk a ⟶ t.G) →* (Over.mk a' ⟶ t.G) where
  toFun w := (Over.homMk g h : Over.mk a' ⟶ Over.mk a) ≫ w
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem pull_left {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a')
    (w : Over.mk a ⟶ t.G) : (pull t g h w).left = g ≫ w.left := rfl

theorem exists_char_of_finPart {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    (e : R ≃+* R') (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R' B]
    (u : Over.mk (spMap (algebraMap R' B) ≫ spMap (e : R →+* R') ≫ x) ⟶ t.G)
    (hu : IsFinPart t (spMap (e : R →+* R') ≫ x) q u)
    (hall : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S]
      (w : Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G), w ^ q = 1 →
        Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left)
    (κ : (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) →* Rˣ) :
    ∃ c : TorsChar t x q, ∀ w, w ^ q = 1 → c.χ R w = κ w := by
  classical
  have he : ∀ (S : Type) [CommRing S] (φ : R →+* S),
      spMap (φ.comp (e.symm : R' →+* R)) ≫ spMap (e : R →+* R') ≫ x = spMap φ ≫ x := fun S _ φ => by
    rw [← Category.assoc, ← sp_comp]
    congr 2
    ext r; simp
  let pt : (B →ₐ[R'] R') → (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) := fun σ =>
    pull t (spMap ((e.symm : R' →+* R).comp σ.toRingHom)) (by
      rw [← he R, ← Category.assoc, ← sp_comp]
      congr 2
      ext r; simp) u
  have hP : spMap (e.symm : R' →+* R) ≫ spMap (RingHom.id R') ≫ spMap (e : R →+* R') ≫ x =
      spMap (algebraMap R R) ≫ x := by
    rw [← he R, ← Category.assoc, ← sp_comp]
  have hpt : ∀ (σ : B →ₐ[R'] R') (w : Over.mk (spMap (RingHom.id R') ≫ spMap (e : R →+* R') ≫ x) ⟶ t.G),
      spMap σ.toRingHom ≫ u.left = w.left → pt σ = pull t _ hP w := fun σ w h => by
    ext1
    rw [pull_left, pull_left, ← h, sp_comp, Category.assoc]
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.T.torsion_character_cocycle_descent E H X t R' (spMap (e : R →+* R') ≫ x) q B u hu
    (fun σ => Units.map (e : R →* R') (κ (pt σ))) (fun σ σ' σ'' w w' h h' h'' => by
      rw [hpt _ _ h, hpt _ _ h', hpt _ _ h'', map_mul, map_mul, map_mul])
  let χ : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S],
      (Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G) → Sˣ := fun S _ _ _ w =>
    if h : Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left then
      Units.map (h.choose : B →* S) b else 1
  have hχ : ∀ (S : Type) [CommRing S] [Algebra R S] [Module.Finite R S]
      (w : Over.mk (spMap (algebraMap R S) ≫ x) ⟶ t.G) (β : B →+* S),
      β.comp (algebraMap R' B) = (algebraMap R S).comp (e.symm : R' →+* R) → spMap β ≫ u.left = w.left →
      (χ S w : S) = β b := fun S _ _ _ w β h₁ h₂ => by
    have h : Thru t u.left ((algebraMap R S).comp (e.symm : R' →+* R)) w.left := ⟨β, h₁, h₂⟩
    have h₃ : h.choose = β := hu.mono S _ _ (h.choose_spec.1.trans h₁.symm) (h.choose_spec.2.trans h₂.symm)
    simp only [χ, dif_pos h, h₃]
    rfl
  refine ⟨⟨χ, ?_, ?_⟩, ?_⟩
  · intro S _ _ _ w w' hw hw'
    obtain ⟨β, h₁, h₂⟩ := hall S w hw
    obtain ⟨β', h₁', h₂'⟩ := hall S w' hw'
    obtain ⟨β'', h₁'', h₂''⟩ := hall S (w * w') (by rw [mul_pow, hw, hw', _root_.one_mul])
    have hc : 𝟙 _ ≫ spMap (algebraMap R S) ≫ x =
        spMap ((algebraMap R S).comp (e.symm : R' →+* R)) ≫ spMap (e : R →+* R') ≫ x := by
      rw [he, Category.id_comp]
    ext
    rw [Units.val_mul, hχ S _ β h₁ h₂, hχ S _ β' h₁' h₂', hχ S _ β'' h₁'' h₂'']
    refine hb₂ S _ (pull t _ hc w) (pull t _ hc w') β β' β'' h₁ h₁' h₁'' ?_ ?_ ?_
    · rw [pull_left, Category.id_comp, h₂]
    · rw [pull_left, Category.id_comp, h₂']
    · rw [← map_mul, pull_left, Category.id_comp, h₂'']
  · intro S S' _ _ _ _ _ _ φ w w' hw h
    obtain ⟨β, h₁, h₂⟩ := hall S w hw
    rw [hχ S _ β h₁ h₂, hχ S' w' (φ.toRingHom.comp β) ?_ ?_]
    · rfl
    · rw [RingHom.comp_assoc, h₁]
      ext r; simp
    · rw [sp_comp, Category.assoc, h₂, h]
  · intro w hw
    obtain ⟨β, h₁, h₂⟩ := hall R w hw
    let σ : B →ₐ[R'] R' :=
      { (e : R →+* R').comp β with
        commutes' := fun r => by
          have := RingHom.congr_fun h₁ r
          simp only [RingHom.comp_apply] at this
          simp [this] }
    have h₃ : pt σ = w := by
      ext1
      rw [pull_left, ← h₂]
      congr 2
      ext r; simp [σ]
    ext
    apply e.injective
    refine (congrArg e (hχ R w β h₁ h₂)).trans ((hb₁ σ).trans ?_)
    rw [h₃]; rfl

theorem exists_char [IsLocallyNoetherian X] {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R]
    [IsLocalRing R] [IsAlgClosed (FractionRing R)] (x : Sp R ⟶ X) (q : ℕ) (hq : q ≠ 0)
    (κ : (Over.mk (spMap (algebraMap R R) ≫ x) ⟶ t.G) →* Rˣ) :
    ∃ c : TorsChar t x q, ∀ w, w ^ q = 1 → c.χ R w = κ w := by
  obtain ⟨f, B, _, _, u, hf, hu, hfib⟩ := GlobalTheory.T.exists_local_finite_torsion_splitting E H X t R x q hq (GlobalTheory.T.splitTors_algClosed_fraction_field E H X t R x q hq)
    (IsLocalRing.maximalIdeal R) inferInstance
  have hf' : IsUnit f := by simpa using hf
  let e : R ≃+* Localization.Away f :=
    (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      (Submonoid.powers_le.2 hf')).toRingEquiv
  have hee : (e : R →+* Localization.Away f) = algebraMap R _ := rfl
  haveI : IsDomain (Localization.Away f) := e.symm.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed (Localization.Away f) := IsIntegrallyClosed.of_equiv e
  refine exists_char_of_finPart t e x q u hu ?_ κ
  intro S _ _ _ w hw
  have hc : 𝟙 _ ≫ spMap (algebraMap R S) ≫ x =
      spMap ((algebraMap R S).comp (e.symm : Localization.Away f →+* R)) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x := by
    rw [Category.id_comp, ← Category.assoc, ← sp_comp, ← hee]
    congr 2
    ext r; simp
  have h := hu.isOpen S _ (pull t _ hc w) (by rw [← map_pow, hw, map_one]) fun 𝔪 h𝔪 => by
    letI := Ideal.Quotient.field 𝔪
    have hd : spMap (Ideal.Quotient.mk 𝔪) ≫ spMap ((algebraMap R S).comp (e.symm : Localization.Away f →+* R)) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x =
        spMap ((Ideal.Quotient.mk 𝔪).comp ((algebraMap R S).comp (e.symm : Localization.Away f →+* R))) ≫
        spMap (algebraMap R (Localization.Away f)) ≫ x := by
      rw [sp_comp _ (Ideal.Quotient.mk 𝔪), Category.assoc]
    refine hfib (S ⧸ 𝔪) _ ?_ (pull t _ hd (pull t _ hc w)) (by rw [← map_pow, ← map_pow, hw, map_one, map_one])
    rw [← IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) 𝔪), ← hee]
    ext r
    rw [RingHom.mem_ker, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  rwa [pull_left, Category.id_comp] at h

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q q' : ℕ), q' ≠ 0 → q ∣ q' → ∀ c : TorsChar t x q, ∃ c' : TorsChar t x q', ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c'.χ B w = c.χ B w := by
  intro E _ _ _ H X _ t C _ _ _ _ x q q' hq' hd c
  haveI := intO_valuationRing C
  haveI := intO_isFractionRing C
  haveI : IsIntegrallyClosed ↥(intO C) := inferInstanceAs (IsIntegrallyClosed ↥(intV C))
  haveI : IsAlgClosed (FractionRing ↥(intO C)) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv ↥(intO C) C).symm.toRingEquiv
  obtain ⟨κ, hκ⟩ := exists_hom_extend (intO_units_root C) q (c.χ ↥(intO C)) (c.mul ↥(intO C))
  obtain ⟨c', hc'⟩ := exists_char t x q' hq' κ
  obtain ⟨m, rfl⟩ := hd
  have up : ∀ {M : Type} [Monoid M] (g : M), g ^ q = 1 → g ^ (q * m) = 1 := fun g h => by
    rw [pow_mul, h, one_pow]
  let c'' : TorsChar t x q :=
    ⟨c'.χ, fun B _ _ _ g g' h h' => c'.mul B g g' (up g h) (up g' h'),
      fun B B' _ _ _ _ _ _ φ g g' h h' => c'.nat B B' φ g g' (up g h) h'⟩
  exact ⟨c', GlobalTheory.T.torsionChar_eq_of_eq_on_torsion E H X t C x q (left_ne_zero_of_mul hq') c'' c fun w hw =>
    (hc' w (up w hw)).trans (hκ w hw)⟩

end GlobalTheory.TorsCharExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def etaL (x : St P) (L : LocAll (lay0 (Dof x))) : ℕ → B.places.Pl → ℚ := L.lay.fixZ.eta

theorem etaL_nonneg (x : St P) (L : LocAll (lay0 (Dof x))) : ∀ j v, 0 ≤ etaL x L j v := L.lay.fixZ.eta_nonneg

def nL (x : St P) (L : LocAll (lay0 (Dof x))) : NStage B w.C (P.q.W (etaL x L) (etaL_nonneg x L)) where
  loc := ((withLoc L).loc)
  locA := ((withLoc L).locA)
  locT := ((withLoc L).locT)
  nd := ((withLoc L).nd)
  ntw := ((withLoc L).ntw)
  naut := ((withLoc L).naut)
  nbc := ((withLoc L).nbc)
  nexp := ((withLoc L).nexp)
  ntypes := ((withLoc L).ntypes)
  nStage_trivialCharacter_compat := ((withLoc L).nStage_trivialCharacter_compat)
  nStage_trivialCharacter_coeff_eq := ((withLoc L).nStage_trivialCharacter_coeff_eq)
  nth := ((withLoc L).nth)
  nbr := ((withLoc L).nbr)
  nbr_ind := ((withLoc L).nbr_ind)
  self_good := ((withLoc L).self_good)
  ntwbr := ((withLoc L).ntwbr)
  ntwbr_ind := ((withLoc L).ntwbr_ind)
  loc_tie := ((withLoc L).loc_tie)
  bc_tie := ((withLoc L).bc_tie)
  rbar_tie := ((withLoc L).rbar_tie)
  mtpar_tie := ((withLoc L).mtpar_tie)
  Z_tie := ((withLoc L).Z_tie)
  Zgood_tie := ((withLoc L).Zgood_tie)
  etaJ_tie := ((withLoc L).etaJ_tie)

def oL (x : St P) (L : LocAll (lay0 (Dof x))) : P.q.Over :=
  ⟨etaL x L, etaL_nonneg x L, { x.o.V with }, { x.o.S with }, nL x L, x.o.G⟩

abbrev DL (x : St P) (L : LocAll (lay0 (Dof x))) : D7 := (w.st (oL x L).Z).toD7

theorem DL_eq (x : St P) (L : LocAll (lay0 (Dof x))) : DL x L = withLoc L := (Eq.refl (withLoc L))

def sameL (x : St P) (L : LocAll (lay0 (Dof x))) : SameGrp (B := B) (C := w.C) x.o.Z (oL x L).Z where
  e k := (Equiv.refl ((Dof x).nd.PlG k))
  pl k v := (Eq.refl ((Dof x).naut.plGw k v))
  e0 g := (Eq.refl ((Dof x).ntypes.e0.coeff g))

def datL (x : St P) (L : LocAll (lay0 (Dof x))) : Dat (w.st (oL x L).Z) w.I P.hX T P.Wt :=
  Dat.transfer (B := B) (C := w.C) (a := x.o.Z) (b := (oL x L).Z) (sameL x L) x.m.z

theorem datL_cG (x : St P) (L : LocAll (lay0 (Dof x))) : HEq (datL x L).cG x.m.z.cG := (HEq.refl x.m.z.cG)
theorem cf_eq (x : St P) (L : LocAll (lay0 (Dof x))) : HEq (TC.cf w.I w.l (oL x L).Z) (cfL L (cfOf x)) := (HEq.refl (cfL L (cfOf x)))

variable {x : St P} (L : LocAll (lay0 (Dof x)))

abbrev YT (x : St P) (L : LocAll (lay0 (Dof x))) (p0 : BaseLevelRowSide (w.D (oL x L).Z)) : Type 1 :=
  Read (datL x L).R.toRealDat (datL x L).F.lv2 p0

structure YRel {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) : Prop where
  rep : HEq (repOf Y) (repOf x.r.Y)
  eW : ∀ i y, HEq (Y.mj.eW i y) (x.r.Y.mj.eW ((i)) ((y)))
  jMt : ∀ μ h i y, HEq (Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1

def kKsL (n : InRat x.r.Y x.m.z.cG) : (datL x L).core.Q.c.F →+* ↥(DL x L).LL0 := (n.kKs)

theorem hkL (n : InRat x.r.Y x.m.z.cG) : ∀ y : (datL x L).core.Q.c.F,
    ((kKsL L n y : ↥(DL x L).LL0) : (DL x L).what₂.LL) = algebraMap (datL x L).core.Q.c.F (DL x L).what₂.LL y := (n.hk)

abbrev SL (n : InRat x.r.Y x.m.z.cG) : RatDat (DL x L).ntw := ratDatR (datL x L).R (datL x L).cG (kKsL L n) (hkL L n)

theorem SL_heq (n : InRat x.r.Y x.m.z.cG) : HEq (ratL L n.S) (SL L n) := (HEq.refl (SL L n))

variable (l : LC hL x)

def ysL : NExpRealS (datL x L).R (datL x L).cG (SL L l.rat) where
  fi := (l.b.YS.fi)
  geq := (l.b.YS.geq)
  rho := (l.b.YS.rho)
  chi := (l.b.YS.chi)
  eF := kc% l.b.YS.eF
  bsup := kc% l.b.YS.bsup
  act := kc% l.b.YS.act

def hkH : NExpRealH x.m.z.R x.m.z.cG l.rat.S l.b.YS where
  hL := l.rat.In.hL
  hs := l.b.Bs.hs
  cHk := fun i b k Q => algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) (l.b.Bs.cHk i b Q) ^ k
  cHk_zero := fun i b Q => pow_zero _
  cHk_unit := fun i b Q =>
    ((l.b.Bs.cHk i b Q).isUnit.map (algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)))).pow 1
  cHk_pow := fun i b k Q => by simp only [pow_one]
  hkEq := by rw [l.b.eF]; exact l.b.Bs.hkEq

def hkHL : NExpRealH (datL x L).R (datL x L).cG (SL L l.rat) (ysL L l) where
  hL := ((hkH l).hL)
  hs := ((hkH l).hs)
  cHk := ((hkH l).cHk)
  cHk_zero := ((hkH l).cHk_zero)
  cHk_unit := ((hkH l).cHk_unit)
  cHk_pow := ((hkH l).cHk_pow)
  hkEq := kc% (hkH l).hkEq

def pvL : ∀ i : Fin (DL x L).R.m, principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (DL x L) i) (DL x L).R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oL x L).Z (l.mt.ad.PV ((i)))) : _))

abbrev cfD (x : St P) (L : LocAll (lay0 (Dof x))) : CharFrame (DL x L) := TC.cf w.I w.l (oL x L).Z

def chD : NChoice (DL x L) := (chL L l.c.ch)

def tpD : TupTied (DL x L) (cfD x L) (chD L l) := (tpL L l.c.tp)

def mtD : MtFam (DL x L) := (mtL L l.mt.M)

def expD (X : NExpTied (withLoc L)) : NExpTied (DL x L) := (X)

def pqD : HeightOneSpectrum (𝓞 (maximalRealSubfield (DL x L).host.E)) → PlE (DL x L).host := (l.Pq)

def eigD : ℕ → (DL x L).what₂.FT → ℕ → PlE (DL x L).host → ↥(DL x L).LL0 := (l.rat.In.eig)

def sbD : Finset (PlE (DL x L).host) := (l.rat.In.Sb)

theorem fitsL : (oL x L).Fits :=
  ⟨⟨(x.fits.div.left), fun _ _ G => kc% (x.fits.div.2 x.o.S x.o.N G)⟩,
    ⟨(x.fits.grp.pl), (x.fits.grp.teich), (x.fits.grp.chi), (x.fits.grp.ser)⟩,
    ⟨(x.fits.grpAt.pl), (x.fits.grpAt.idem), (x.fits.grpAt.cen)⟩,
    fun eR h => ⟨((x.fits.cen eR h).amb), ((x.fits.cen eR h).mt)⟩⟩

theorem bkL : BkLaw (w.D (oL x L).Z) := (x.bk)

theorem okL : ∀ v, TwistedAt (DL x L) v → IntegralHeckeForms.TwOK ((chD L l).twI v) ((chD L l).k' v) ((chD L l).Q v)
    (((chD L l).psi' v).comp ((DL x L).ntw.art ((chD L l).twI v) ((chD L l).Q v))) := (l.c.ok)

theorem geoL : Nonempty (GlobalTheory.GeoTie.ThetaTie (ysL L l) (datL x L).geo.fw (DL x L).nth) := by
  obtain ⟨g⟩ := l.b.geo
  exact ⟨⟨fun i j b => ⟨((g.side i j b).pt), ((g.side i j b).cover),
    ((g.side i j b).ev_eq), kc% (g.side (kc% i) (kc% j) b).fmUr, (by with_unfolding_all exact ((g.side ((i)) ((j)) b).hk : _)),
    ((g.side i j b).hk_none)⟩, (g.isUnramified₂)⟩⟩

theorem sameGaloisL : GlobalTheory.TwistChoice.SameGalois (Dof x).nd (DL x L).nd :=
  ⟨(Eq.refl (Dof x).R), (HEq.refl (Dof x).host), (Eq.refl (Dof x).loc),
    (HEq.refl (Dof x).nd.Om), (HEq.refl (Dof x).nd.instOm),
    (HEq.refl (Dof x).nd.algOm), (HEq.refl (Dof x).nd.plOm),
    (HEq.refl (Dof x).nd.PlG)⟩

theorem twistDataAgreeAcrossCoefficients_localized : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients (Dof x).ntw (DL x L).ntw :=
  ⟨(HEq.refl (Dof x).ntw.cc), (HEq.refl (Dof x).ntw.Tw), (HEq.refl (Dof x).ntw.l),
    (HEq.refl (Dof x).ntw.O0), (HEq.refl (Dof x).ntw.crO0), (HEq.refl (Dof x).ntw.algO0),
    (HEq.refl (Dof x).ntw.topO0), (HEq.refl (Dof x).ntw.O), (HEq.refl (Dof x).ntw.crO),
    (HEq.refl (Dof x).ntw.algO), (HEq.refl (Dof x).ntw.Ok), (HEq.refl (Dof x).ntw.crOk),
    (HEq.refl (Dof x).ntw.algOk), (HEq.refl (Dof x).ntw.zk), (HEq.refl (Dof x).ntw.pD),
    (HEq.refl (Dof x).ntw.chi1), (HEq.refl (Dof x).ntw.Sig), (HEq.refl (Dof x).ntw.finSig),
    (HEq.refl (Dof x).ntw.jS), (HEq.refl (Dof x).ntw.side), (HEq.refl (Dof x).ntw.rhoS),
    (HEq.refl (Dof x).ntw.S0), (HEq.refl (Dof x).ntw.hEig), (HEq.refl (Dof x).ntw.abelian₂),
    (HEq.refl (Dof x).ntw.sideL), (HEq.refl (Dof x).ntw.RCG), (HEq.refl (Dof x).ntw.grpRCG),
    (HEq.refl (Dof x).ntw.finRCG), (HEq.refl (Dof x).ntw.art), (HEq.refl (Dof x).ntw.th)⟩

theorem sameFormsL : GlobalTheory.TwistChoice.SameForms (Dof x).nexp (DL x L).nexp :=
  ⟨(HEq.refl (Dof x).nexp.Fm), (HEq.refl (Dof x).nexp.acgFm), (HEq.refl (Dof x).nexp.modFmK),
    (HEq.refl (Dof x).nexp.modFmO), (HEq.refl (Dof x).nexp.actG), (HEq.refl (Dof x).nexp.U),
    (HEq.refl (Dof x).nexp.psiU), (HEq.refl (Dof x).nexp.eAlg), (HEq.refl (Dof x).nexp.Dat),
    (HEq.refl (Dof x).nexp.th), (HEq.refl (Dof x).nexp.lev), (HEq.refl (Dof x).nexp.thPsi),
    (HEq.refl (Dof x).nexp.MtV), (HEq.refl (Dof x).nexp.acgMt), (HEq.refl (Dof x).nexp.modMtK),
    (HEq.refl (Dof x).nexp.modMtO), (HEq.refl (Dof x).nexp.MtLat), (HEq.refl (Dof x).nexp.thP),
    (HEq.refl (Dof x).nexp.hkF)⟩

theorem keptL : Kept l.c.ch (chD L l) :=
  ⟨sameGaloisL L, twistDataAgreeAcrossCoefficients_localized L, sameFormsL L, (HEq.refl (Dof x).ntwbr), (HEq.refl l.c.ch.twI), (HEq.refl l.c.ch.sd),
    (HEq.refl l.c.ch.Q), (HEq.refl l.c.ch.k'), (HEq.refl l.c.ch.psi')⟩

def xdD (xd : ThData (Dof x)) : ThData (DL x L) := ⟨(xd.xd0), (xd.thetaBase_invariant_action)⟩

theorem xdD_all {xd : ThData (Dof x)} (h : XdAll xd) : XdAll (xdD L xd) := (h)

theorem ysL_fi : ∀ i y, HEq (((ysL L l).fi i).e y) y := (l.b.fi)

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem valLL0_colW {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
  rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
  subst C_eq
  exact val _ _ _ _ _ _

theorem valLL0_allSt : PrN → AllSt fun _ _ _ _ _ _ x => ValLL0 (Dof x) (cfOf x) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x => ?_
  exact valLL0_colW w x.o.Z

end GlobalTheory.HeightCounting.Up
end

