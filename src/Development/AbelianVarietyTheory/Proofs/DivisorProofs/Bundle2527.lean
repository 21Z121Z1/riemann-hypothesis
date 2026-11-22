import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)}

theorem existsUnique_pt_of_triv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) :
    ∃! y : Pt X T.B, spMap T.π ≫ y.left = T.x := by
  have hb : Function.Bijective T.π :=
    ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ by simpa [hT] using (T.ker b).1 hb, T.surj⟩
  let e := RingEquiv.ofBijective T.π hb
  let ρ : T.B₀ →+* T.B := e.symm.toRingHom
  have h1 : ρ.comp T.π = RingHom.id _ := RingHom.ext e.symm_apply_apply
  have h2 : T.π.comp ρ = RingHom.id _ := RingHom.ext e.apply_symm_apply
  have k1 : spMap ρ ≫ spMap T.π = 𝟙 _ := by rw [← Cris.spMap_comp, h1, Cris.spMap_id]
  have k2 : spMap T.π ≫ spMap ρ = 𝟙 _ := by rw [← Cris.spMap_comp, h2, Cris.spMap_id]
  have hw : (spMap ρ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B) := by
    have : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      (congrArg (T.x ≫ ·) (Category.comp_id X.hom)).symm.trans T.w
    rw [Category.assoc, this, Cris.spMap_comp, ← Category.assoc, k1, Category.id_comp]
  refine ⟨Over.homMk (spMap ρ ≫ T.x) hw, ?_, fun y hy ↦ Over.OverMorphism.ext ?_⟩
  · change spMap T.π ≫ spMap ρ ≫ T.x = T.x
    rw [← Category.assoc, k2, Category.id_comp]
  · change y.left = spMap ρ ≫ T.x
    rw [← hy, ← Category.assoc, k1]
    exact (Category.id_comp _).symm

def liftHom (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (y : Pt X T.B) (h : spMap T.π ≫ y.left = T.x) : trivAt y ⟶ T :=
  Thick.trivHom (AlgHom.id R T.B) h

theorem mem_hodgeFiltration_iff_pointwiseCoboundary (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    CatCoh.H1.mk _ f ∈ F1 (X.hom ≫ 𝟙 _) ↔ ∃ k : Fn0 X, IsCob (whole X) (fv f) k := by
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    refine ⟨fun D _ _ x ↦ g ⟨trivAt x, rfl⟩, fun D _ _ D' _ _ φ x _ ↦ ?_⟩
    exact (congrFun (congrFun (congrFun hg ⟨trivAt x, rfl⟩) ⟨trivAt (spOver φ ≫ x), rfl⟩) ⟨trivMap φ x⟩).symm
  · rintro ⟨k, hk⟩
    choose y hy hu using existsUnique_pt_of_triv (R := R) (X := X)
    refine H1.mk_eq_zero.2 ⟨fun T ↦ (k T.obj.B (y T.obj T.property) +
      ev f (liftHom T.obj _ (hy T.obj T.property)) : T.obj.B), ?_⟩
    funext ⟨T, hT⟩ ⟨T', hT'⟩ ⟨φ⟩
    have h' : spMap T'.π ≫ (spOver φ.φ ≫ y T hT).left = T'.x := by
      change spMap T'.π ≫ spMap (φ.φ : T.B →+* T'.B) ≫ (y T hT).left = T'.x
      rw [← φ.pt, ← hy T hT, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
      congr 2
      exact RingHom.ext fun b ↦ (φ.comm b).symm
    have key : ∀ (z : Pt X T'.B) (hz : spMap T'.π ≫ z.left = T'.x), spOver φ.φ ≫ y T hT = z →
        k T'.B z + ev f (liftHom T' z hz) - φ.φ (k T.B (y T hT) + ev f (liftHom T _ (hy T hT))) = ev f φ := by
      rintro _ hz rfl
      have e1 := ev_sq f (trivMap φ.φ (y T hT)) (liftHom T' _ hz) (liftHom T _ (hy T hT)) φ fun _ ↦ rfl
      have e2 := hk T.B T'.B φ.φ (y T hT) (sm_whole _)
      change fv f T.B T'.B φ.φ (y T hT) + _ = _ at e1
      rw [map_add]
      linear_combination e1 - e2
    exact key _ (hy T' hT') (hu T' hT' _ h')

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltrationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S : Sys I π s₀, RhoBC hI hk s₀ → S.Full hI → ∀ c : Cr hI π s₀, c ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) ↔ rho hI hk s₀ c ∈ F1 s₀ := by
  first | exact @GlobalTheory.LiftSys.Sys.mem_K_sup_iff | exact GlobalTheory.LiftSys.Sys.mem_K_sup_iff | (intros; apply GlobalTheory.LiftSys.Sys.mem_K_sup_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapIdealSheafOfForallDivLocalEquationStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_map_idealSheaf_of_forall_div_localEquation : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), (∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → valF M₁.pt V.1 g / f' ∈ M.O x') → g ∈ (D.idealSheaf.map π).ideal V := by
  first | exact @GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div | exact GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div | (intros; apply GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOneIffIsIntegral
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_isIntegral (a : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * a) := by
  have h : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  rw [zsmul_eq_mul] at hi
  rw [Nat.cast_natAbs]
  rcases abs_choice k with h | h <;> rw [h]
  · exact hi
  · push_cast; rw [neg_mul]; exact hi.neg

theorem mem_one_iff_isIntegral (a : maximalRealSubfield E) :
    a ∈ (1 : Submodule (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ↔ IsIntegral ℤ (a : E) := by
  rw [Submodule.mem_one]
  have e : IsIntegral ℤ (a : E) ↔ IsIntegral ℤ a :=
    isIntegral_algebraMap_iff (R := ℤ) (A := maximalRealSubfield E) (B := E) (x := a) Subtype.val_injective
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def passMul (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (n : ℕ) : GlobalTheory.HilbFam.Lat (maximalRealSubfield E) where
  carrier := {x | ∃ y' ∈ lattice c y, (n : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨u, hu, e⟩ ⟨u', hu', e'⟩ => ⟨u + u', (latticeSub c y).add_mem hu hu', by
    rw [mul_add, e, e']; simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨u, hu, e⟩ => ⟨algebraMap (OF E) E a * u, mul_mem_lattice (algebraMap_mem_orderC c a) hu, by
    rw [ptE_smul, ← e]; ring⟩

theorem exists_coord_integral [IsCMField E] {θ : E} (hθ : θ ∉ maximalRealSubfield E) :
    ∃ k : ℕ, 0 < k ∧ ∀ (z : E) (a b : maximalRealSubfield E), IsIntegral ℤ z → (k : E) * z = (a : E) * θ + b →
      IsIntegral ℤ (a : E) ∧ IsIntegral ℤ (b : E) := by
  set σ := IsCMField.complexConj E with hσ
  have hδ : θ - σ θ ≠ 0 := fun h => hθ ((IsCMField.complexConj_eq_self_iff E θ).1 (sub_eq_zero.1 h).symm)
  obtain ⟨k₁, h₁, i₁⟩ := exists_nat_mul_isIntegral (θ - σ θ)⁻¹
  obtain ⟨k₂, h₂, i₂⟩ := exists_nat_mul_isIntegral θ
  refine ⟨k₁ * k₂, Nat.mul_pos h₁ h₂, fun z a b hz e => ?_⟩
  have hσz : IsIntegral ℤ (σ z) := hz.map (σ : E →+* E).toIntAlgHom
  have ea : σ (a : E) = a := σ.commutes a
  have eb : σ (b : E) = b := σ.commutes b
  have e' : ((k₁ * k₂ : ℕ) : E) * σ z = (a : E) * σ θ + b := by
    have := congrArg σ e
    rwa [map_mul, map_add, map_mul, map_natCast, ea, eb] at this
  push_cast at e e'
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have ha : (a : E) = k₂ * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    field_simp
    linear_combination e' - e
  refine ⟨ha ▸ (hn k₂).mul (i₁.mul (hz.sub hσz)), ?_⟩
  have hb : (b : E) = k₁ * (k₂ * z) - (k₂ * θ) * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    linear_combination -e - θ * ha
  exact hb ▸ ((hn k₁).mul ((hn k₂).mul hz)).sub (i₂.mul (i₁.mul (hz.sub hσz)))

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N₀ : ℕ),
    c ≠ ⊥ → θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) → 0 < N₀ →
    ∃ (n N : ℕ) (L : GlobalTheory.HilbFam.Lat (maximalRealSubfield E)), 0 < n ∧ 0 < N ∧ N₀ ∣ N ∧ GlobalTheory.HilbFam.HasLevel N L ∧
      ∀ x : Fin 2 → maximalRealSubfield E, x ∈ L ↔ ∃ y' ∈ lattice c y,
        (n : E) * y' = ((x 0 : maximalRealSubfield E) : E) * θ + ((x 1 : maximalRealSubfield E) : E) := by
  intro E _ _ _ θ c y N₀ hc hθ hN₀
  obtain ⟨M, hM, hlo, hhi⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y
  obtain ⟨k, hk, hco⟩ := exists_coord_integral (θ := θ) fun h => hθ ⟨⟨θ, h⟩, rfl⟩
  obtain ⟨D, hD, iD⟩ := exists_nat_mul_isIntegral θ
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  refine ⟨k * M, N₀ * (k * M * M * D), passMul θ c y (k * M), by positivity, by positivity, dvd_mul_right _ _,
    ⟨fun x hx => ?_, fun x hx => ?_⟩, fun x => Iff.rfl⟩
  · have h0 := (mem_one_iff_isIntegral _).1 (hx 0 trivial)
    have h1 := (mem_one_iff_isIntegral _).1 (hx 1 trivial)
    have hi : IsIntegral ℤ ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E))) :=
      (hn N₀).mul ((h0.mul iD).add ((hn D).mul h1))
    refine ⟨_, hlo ⟨_, hi⟩, ?_⟩
    rw [ptE_smul, map_natCast]
    show ((k * M : ℕ) : E) * ((M : E) * ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E)))) = _
    simp only [ptE]
    push_cast
    ring
  · obtain ⟨u, hu, e⟩ := hx
    obtain ⟨h0, h1⟩ := hco (M * u) (x 0) (x 1) (hhi u hu) (by rw [← mul_assoc, ← Nat.cast_mul]; exact e)
    intro i _
    fin_cases i
    · exact (mem_one_iff_isIntegral _).2 h0
    · exact (mem_one_iff_isIntegral _).2 h1

end GlobalTheory.RoadE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AffDesc

open TensorProduct

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem isoPushout_desc_tmul {R0 A B : Type} [CommRing R0] [CommRing A] [CommRing B] [Algebra R0 A]
    [Algebra R0 B] {D : CommRingCat.{0}} (u : CommRingCat.of A ⟶ D) (v : CommRingCat.of B ⟶ D)
    (w : CommRingCat.ofHom (algebraMap R0 A) ≫ u = CommRingCat.ofHom (algebraMap R0 B) ≫ v) (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R0 A B).isoPushout.hom ≫ pushout.desc u v w).hom (a ⊗ₜ b) =
      u.hom a * v.hom b := by
  have e : a ⊗ₜ[R0] b = Algebra.TensorProduct.includeLeftRingHom a *
      Algebra.TensorProduct.includeRight.toRingHom b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, map_mul]
  have h1 := congrArg (fun φ => φ.hom a)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inl_isoPushout_hom =≫ pushout.desc u v w)
  have h2 := congrArg (fun φ => φ.hom b)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inr_isoPushout_hom =≫ pushout.desc u v w)
  simp only [Category.assoc, pushout.inl_desc, pushout.inr_desc, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at h1 h2
  rw [← h1, ← h2]
  rfl

theorem appLE_apply_appLE {X Y Y' Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (U : Z.Opens) (V : Y.Opens) (V' : Y'.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e₁' : V' ≤ g' ⁻¹ᵁ U) (e₂' : W ≤ f' ⁻¹ᵁ V') (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (f'.appLE V' W e₂').hom ((g'.appLE U V' e₁').hom x) := by
  have a := Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂
  have b := Scheme.Hom.appLE_comp_appLE f' g' U V' W e₁' e₂'
  have c := appLE_eq_of_eq h U W (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂ (Scheme.Hom.preimage_mono f e₁))
    (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂' (Scheme.Hom.preimage_mono f' e₁'))
  exact congrArg (fun φ => CommRingCat.Hom.hom φ x) (a.trans (c.trans b.symm))

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appTop = f.appLE ⊤ ⊤ le_top :=
  Scheme.Hom.app_eq_appLE f

end GlobalTheory.Mum.AffDesc

namespace GlobalTheory.Mum.AffDesc
open TensorProduct

theorem mem_range_app_of_flat : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ S Y Z π y p q hπ hy H r h1 h2 hP hx V hV f hf
  classical
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  haveI : QuasiSeparatedSpace S := (quasiSeparated_iff_quasiSeparatedSpace π).1 inferInstance
  haveI : CompactSpace (pullback π π : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst π π ≫ π)
  have hUY1 : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hUY2 : pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) = r ⁻¹ᵁ ⊤ ⊓ (pullback.fst p p ≫ p) ⁻¹ᵁ V := by
    simp [Scheme.Hom.comp_preimage]
  have i1 := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY1 (isAffineOpen_top _) hV isCompact_univ isQuasiSeparated_univ
  have m2 := mono_pushoutSection_of_isCompact_of_flat_right hP (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY2 (isAffineOpen_top _) hV isCompact_univ
  letI aB : Algebra Γ(Sp R, ⊤) Γ(S, ⊤) := (π.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI aA : Algebra Γ(Sp R, ⊤) Γ(Y, V) := (y.appLE ⊤ V le_top).hom.toAlgebra
  letI aC : Algebra Γ(Sp R, ⊤) Γ(pullback π π, ⊤) := ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top).hom.toAlgebra
  haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V) := y.flat_appLE (isAffineOpen_top _) hV le_top
  let ΦB := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(S, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection H.flip (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY1
  let ΦC := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(pullback π π, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection hP (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY2
  have hB : Function.Surjective ΦB.hom := by
    have : IsIso ΦB := by dsimp only [ΦB]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso ΦB).2
  have hC : Function.Injective ΦC.hom := by
    have : Mono ΦC := by dsimp only [ΦC]; infer_instance
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback ΦC).1 this
  have fB : ∀ (b : Γ(S, ⊤)) (a : Γ(Y, V)), ΦB.hom (b ⊗ₜ a) =
      (q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b * (p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a :=
    fun b a => isoPushout_desc_tmul _ _ _ b a
  have fC : ∀ (c : Γ(pullback π π, ⊤)) (a : Γ(Y, V)), ΦC.hom (c ⊗ₜ a) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom c *
        ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun c a => isoPushout_desc_tmul _ _ _ c a
  have k1 : ∀ x, (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.fst π π) π ⊤ ⊤ ⊤ le_top le_top)
  have k2 : ∀ x, (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.snd π π) π ⊤ ⊤ ⊤ le_top le_top)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ x) (appLE_eq_of_eq (pullback.condition (f := π) (g := π)).symm _ _ _ _))
  let d : Γ(S, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(pullback π π, ⊤) :=
    { toFun := fun x => (pullback.fst π π).appLE ⊤ ⊤ le_top x - (pullback.snd π π).appLE ⊤ ⊤ le_top x
      map_add' := fun x x' => by simp only [map_add]; abel
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, k1, k2, RingHom.id_apply]
        ring }
  have hex : Function.Exact (Algebra.linearMap Γ(Sp R, ⊤) Γ(S, ⊤)) d := by
    intro x
    constructor
    · intro h0
      have e0 : (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x := by
        rw [appTop_eq_appLE, appTop_eq_appLE]; exact sub_eq_zero.1 h0
      obtain ⟨c, hc⟩ := hx x e0
      refine ⟨c, ?_⟩
      rw [appTop_eq_appLE] at hc
      exact hc
    · rintro ⟨c, rfl⟩
      show (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) -
        (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) = 0
      rw [k1, k2, sub_self]
  have hex' := Module.Flat.rTensor_exact Γ(Y, V) hex
  have hEq : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have c1 : ∀ b, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b) :=
    fun b => by
      rw [Scheme.Hom.app_eq_appLE]
      exact appLE_apply_appLE (pullback.fst p p) q r (pullback.fst π π) h1.symm ⊤ (p ⁻¹ᵁ V) ⊤
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) le_rfl le_top (by simp) b
  have c2 : ∀ b, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.snd π π).appLE ⊤ ⊤ le_top b) :=
    fun b => appLE_apply_appLE (pullback.snd p p) q r (pullback.snd π π) h2.symm ⊤ (p ⁻¹ᵁ V) ⊤
      (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) hEq.ge le_top (by simp) b
  have c3 : ∀ a, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => by
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun φ => CommRingCat.Hom.hom φ a)
        (Scheme.Hom.appLE_comp_appLE (pullback.fst p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl le_rfl)
  have c4 : ∀ a, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => (congrArg (fun φ => CommRingCat.Hom.hom φ a)
      (Scheme.Hom.appLE_comp_appLE (pullback.snd p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl hEq.ge)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ a) (appLE_eq_of_eq (pullback.condition (f := p) (g := p)).symm V
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) _ _))
  have key : ∀ t, ΦC.hom (d.rTensor Γ(Y, V) t) = ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom (ΦB.hom t) -
      ((pullback.snd p p).appLE _ _ hEq.ge).hom (ΦB.hom t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      rw [LinearMap.rTensor_tmul, fC, fB, map_mul, map_mul, c1, c2, c3, c4]
      change (r.appLE _ _ _).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b - (pullback.snd π π).appLE ⊤ ⊤ le_top b) * _ = _
      rw [map_sub, sub_mul]
    | add t t' ht ht' =>
      rw [map_add, map_add, ht, ht', map_add, map_add, map_add]
      abel
  obtain ⟨t, rfl⟩ := hB f
  have hz : d.rTensor Γ(Y, V) t = 0 := hC (by rw [key, map_zero, hf hEq, sub_self])
  obtain ⟨s, rfl⟩ := (hex' t).1 hz
  clear hf hz key
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c a =>
    rw [LinearMap.rTensor_tmul, fB]
    refine ⟨(y.appLE ⊤ V le_top).hom c * a, ?_⟩
    rw [map_mul, Scheme.Hom.app_eq_appLE]
    congr 1
    exact appLE_apply_appLE p y q π H.w ⊤ V ⊤ (p ⁻¹ᵁ V) le_top le_rfl le_top (by simp) c
  | add s s' hs hs' =>
    obtain ⟨u, hu⟩ := hs
    obtain ⟨u', hu'⟩ := hs'
    exact ⟨u + u', by rw [map_add, hu, hu', map_add, map_add]⟩

end GlobalTheory.Mum.AffDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppTopOfFibreSquareProjectionsEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open scoped TensorProduct

namespace GlobalTheory.Mum

theorem mem_range_of_tmul_eq_tmul {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A]
    [IsDomain A] [Algebra R A] (hinj : Function.Injective (algebraMap R A)) (a : A) (ha : IsIntegral R a)
    (h : algebraMap A (FractionRing A) a ⊗ₜ[R] (1 : FractionRing A) =
      (1 : FractionRing A) ⊗ₜ[R] algebraMap A (FractionRing A) a) :
    a ∈ Set.range (algebraMap R A) := by
  have hRL : Function.Injective (algebraMap R (FractionRing A)) := by
    rw [IsScalarTower.algebraMap_eq R A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp hinj
  haveI : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective R _).mpr hRL
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  haveI := FractionRing.isScalarTower_liftAlgebra R (FractionRing A)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing R) (FractionRing A))
    (LinearMap.ker_eq_bot.mpr (algebraMap (FractionRing R) (FractionRing A)).injective)
  have hφ1 : φ 1 = 1 := by simpa using congr($hφ 1)
  let Φ : FractionRing A ⊗[R] FractionRing A →ₗ[R] FractionRing A :=
    LinearMap.mul' R (FractionRing A) ∘ₗ
      TensorProduct.map ((Algebra.linearMap (FractionRing R) (FractionRing A) ∘ₗ φ).restrictScalars R) LinearMap.id
  have key := congr(Φ $h)
  simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, LinearMap.id_apply, LinearMap.mul'_apply, hφ1, map_one] at key
  replace key : algebraMap (FractionRing R) (FractionRing A) (φ (algebraMap A (FractionRing A) a)) =
      algebraMap A (FractionRing A) a := by
    convert key using 1
    · exact (_root_.mul_one _).symm
    · exact (_root_.one_mul _).symm
  have hint : IsIntegral R (φ (algebraMap A (FractionRing A) a)) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing A))
      (algebraMap (FractionRing R) (FractionRing A)).injective]
    change IsIntegral R (algebraMap (FractionRing R) (FractionRing A) _)
    rw [key]
    exact ha.map (IsScalarTower.toAlgHom R A (FractionRing A))
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A), hr, key]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_range_appTop_of_fst_eq_snd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → IsIntegral S → Function.Injective π.appTop.hom → ∀ x : Γ(S, ⊤),
    (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom := by
  intro R _ _ _ S π hP hI hinj x hx
  obtain ⟨s⟩ : Nonempty S := hI.nonempty
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨s, hsU⟩⟩
  let res := S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  have hres : Function.Injective res.hom := map_injective_of_isIntegral S _
  have happ : ∀ t, (π.appLE ⊤ U le_top).hom t = res.hom (π.appTop.hom t) := fun t => rfl
  let ρ : R →+* Γ(S, U) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appLE ⊤ U le_top).hom
  letI : Algebra R Γ(S, U) := ρ.toAlgebra
  have hρ : ∀ t, (π.appLE ⊤ U le_top).hom t = algebraMap R Γ(S, U) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t) := by
    intro t
    change _ = ρ _
    simp only [ρ, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) t).symm
  have hρinj : Function.Injective (algebraMap R Γ(S, U)) := by
    intro a b hab
    have h1 : ∀ c, algebraMap R Γ(S, U) c = res.hom (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
      fun c => rfl
    rw [h1, h1] at hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective (hinj (hres hab))
  haveI : UniversallyClosed π := inferInstance
  have hxint : IsIntegral R (res.hom x) := by
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed π x
    refine ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap R Γ(S, U)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = res.hom.comp π.appTop.hom := by
      ext t
      exact (hρ t).symm.trans (happ t)
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  have H : IsPullback (pullback.fst π π) (pullback.snd π π) π π := IsPullback.of_hasPullback π π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := U) (UX := U) le_top le_top rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top rfl (isAffineOpen_top _) hU hU)
  let j₁ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  let j₂ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    (Algebra.TensorProduct.includeRight : FractionRing Γ(S, U) →ₐ[R] _).toRingHom.comp
      (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  have hw : π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₁ : Γ(S, U) ⟶ CommRingCat.of _) =
      π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₂ : Γ(S, U) ⟶ CommRingCat.of _) := by
    ext t
    change j₁ ((π.appLE ⊤ U le_top).hom t) = j₂ ((π.appLE ⊤ U le_top).hom t)
    rw [hρ]
    show algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _) ⊗ₜ[R] (1 : FractionRing Γ(S, U)) =
      (1 : FractionRing Γ(S, U)) ⊗ₜ[R] algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _)
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hd1 := congr(($(po.inl_desc _ _ hw)).hom (res.hom x))
  have hd2 := congr(($(po.inr_desc _ _ hw)).hom (res.hom x))
  have e1 : ∀ (f : pullback π π ⟶ S) (h : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ f ⁻¹ᵁ U),
      (f.appLE U _ h).hom (res.hom x) =
        ((pullback π π).presheaf.map (homOfLE (le_top : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ ⊤)).op).hom
          (f.appTop.hom x) := by
    intro f h
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hj : j₁ (res.hom x) = j₂ (res.hom x) := by
    refine hd1.symm.trans (Eq.trans ?_ hd2)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, e1, e1, hx]
  obtain ⟨r, hr⟩ := mem_range_of_tmul_eq_tmul hρinj _ hxint hj
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, hres ?_⟩
  rw [← happ]
  exact hr

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSignsStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_realLie_iff_traceFree_skew_signs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r), Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | exact GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) [IsLocallyNoetherian T.left] (lv : D.La → (T ⟶ o.A)), (∀ x y, lv (x + y) = lv x * lv y) → (∀ x, lv (N' • x) = 1) → (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) → ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ T.left) (x' : Sp k' ⟶ T.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ((∃ I : TateIsoO D k (Over.mk (x ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y) ↔ (∃ I : TateIsoO D k' (Over.mk (x' ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x' rfl : Over.mk (x' ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y)) := by
  first | exact @GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes | exact GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes | (intros; apply GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes; all_goals assumption)
end

