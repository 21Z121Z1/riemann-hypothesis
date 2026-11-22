import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomZeroEquivContinuous
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Model

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

theorem galMap_geomMap {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    (u : X ⟶ Y) (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω p σ ≫ geomMap Ω p u hu = geomMap Ω p u hu ≫ galMap Ω q σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, galMap_fst, geomMap, pullback.lift_fst, ← Category.assoc, galMap_fst]
  · rw [Category.assoc, Category.assoc, galMap_snd, geomMap, pullback.lift_snd, pullback.lift_snd_assoc, galMap_snd]

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem gal_pull {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    (u : X ⟶ Y) (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) (n : ℕ) (x : H R n (geom Ω q)) :
    gal R Ω p n σ (pull R n (geomMap Ω p u hu) x) = pull R n (geomMap Ω p u hu) (gal R Ω q n σ x) := by
  change pull R n (galMap Ω p σ) (pull R n (geomMap Ω p u hu) x) =
    pull R n (geomMap Ω p u hu) (pull R n (galMap Ω q σ) x)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← pull_comp, ← pull_comp, galMap_geomMap]

theorem coefPre_isSheaf : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  haveI : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} R))) :=
    reflectsLimitsOfSize_shrink.{1, 0, 0, 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{1} (ULift.{1} R)))
  have h := (isSheaf_fpqcTopology_continuousMapPresheaf.{0} R).of_le Scheme.proetaleTopology_le_fpqcTopology
  have e : coefPre R ⋙ forget (ModuleCat.{1} (ULift.{1} R)) = continuousMapPresheaf.{0} R ⋙ uliftFunctor.{1} := rfl
  rw [e]
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _ h

def coefIso : coef R ≅ (⟨coefPre R, coefPre_isSheaf R⟩ : Shv R) :=
  (asIso (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app
    ⟨coefPre R, coefPre_isSheaf R⟩

def homEquiv (X : Scheme.{0}) : ((freeOn R).obj X ⟶ coef R) ≃ C(X, R) := by
  refine (Iso.homCongr (Iso.refl _) (coefIso R)).trans ?_
  refine ((sheafificationAdjunction _ _).homEquiv _ _).trans ?_
  refine (((ModuleCat.adj (ULift.{1} R)).whiskerRight (C := Scheme.{0}ᵒᵖ)).homEquiv _ _).trans ?_
  refine uliftYonedaEquiv.trans ?_
  exact Equiv.ulift

def cohomZeroEquivContinuous (X : Scheme.{0}) : H R 0 X ≃ C(X, R) :=
  Abelian.Ext.homEquiv₀.trans (homEquiv R X)

theorem cohomZero_nontrivial (X : Scheme.{0}) [Nonempty X] [Nontrivial R] : Nontrivial (H R 0 X) :=
  (cohomZeroEquivContinuous R X).nontrivial

example : Nontrivial (H ℤ_[3] 0 (Spec (CommRingCat.of ℚ))) := cohomZero_nontrivial _ _
example : Nontrivial (H (ZMod 5) 0 (Spec (CommRingCat.of ℚ))) := by
  haveI : Fact (1 < 5) := ⟨by norm_num⟩
  exact cohomZero_nontrivial _ _

end GlobalTheory.Et.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
section
noncomputable section

namespace GlobalTheory.Cong

variable {k : Type} [NormedField k]

def PolyApprox [IsUltrametricDist k] {J : Type} (θ : J → k) (S : Set (J → k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

def trc {Γ A : Type} [Group Γ] [CommRing A] {a : ℕ} (r : Γ →* GL (Fin a) A) (g : Γ) : A :=
  ((r g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).trace

def LinApprox {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C ∧
    ∀ g : Γ, ‖trc r g - ∑ ρ ∈ s, c ρ * trc ρ g‖ ≤ ε

def opOf {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) (v : V) : V :=
  f.sum fun g c => c • ρ g v

theorem linApprox_of_mem {Γ : Type} [Group Γ] {a : ℕ} {r : Γ →* GL (Fin a) k} {C : Set (Γ →* GL (Fin a) k)} (h : r ∈ C) :
    LinApprox r C := fun ε hε =>
  ⟨{r}, fun _ => 1, by simpa using h, fun g => by simpa using hε.le⟩

theorem PolyApprox.mono [IsUltrametricDist k] {J : Type} {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hST : S ⊆ T) : PolyApprox θ T := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hST, hP⟩

theorem LinApprox.mono {Γ : Type} [Group Γ] {a : ℕ} {r : Γ →* GL (Fin a) k} {C D : Set (Γ →* GL (Fin a) k)}
    (h : LinApprox r C) (hCD : C ⊆ D) : LinApprox r D := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hCD, hP⟩

variable [NormOneClass k] [IsUltrametricDist k]

theorem aeval_sub_le {J : Type} {x y : J → k} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1)
    (hxy : ∀ j, ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖MvPolynomial.aeval x P‖ ≤ 1 ∧ ‖MvPolynomial.aeval y P‖ ≤ 1 ∧
      ‖MvPolynomial.aeval x P - MvPolynomial.aeval y P‖ ≤ δ := by
  first
  | exact @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | (apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le ..)

theorem polyApprox_of_uniform {J : Type} {θ : J → k} {S : Set (J → k)} (hθ : ∀ j, ‖θ j‖ ≤ 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ η ∈ S, (∀ j, ‖η j‖ ≤ 1) ∧ ∀ j, ‖θ j - η j‖ ≤ ε) : PolyApprox θ S := fun ε hε => by
  obtain ⟨η, hηS, hη1, hθη⟩ := h ε hε
  refine ⟨{η}, fun _ => 1, by simpa using hηS, fun P => ?_⟩
  simpa using (aeval_sub_le hε.le hθ hη1 hθη P).2.2

theorem polyApprox_zero_padic (p : ℕ) [Fact p.Prime] :
    PolyApprox (fun _ : Unit => (0 : ℚ_[p])) {θ | ∃ n : ℕ, θ = fun _ => (p : ℚ_[p]) ^ (n + 1)} ∧
      (fun _ : Unit => (0 : ℚ_[p])) ∉ {θ : Unit → ℚ_[p] | ∃ n : ℕ, θ = fun _ => (p : ℚ_[p]) ^ (n + 1)} := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpn : ∀ n : ℕ, ‖(p : ℚ_[p]) ^ n‖ = ((p : ℝ)⁻¹) ^ n := fun n => by rw [norm_pow, Padic.norm_p]
  constructor
  · refine polyApprox_of_uniform (fun _ => by simp) fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
    refine ⟨fun _ => (p : ℚ_[p]) ^ (n + 1), ⟨n, rfl⟩, fun _ => ?_, fun _ => ?_⟩
    · rw [hpn]; exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp.le)
    · rw [zero_sub, norm_neg, hpn]
      calc ((p : ℝ)⁻¹) ^ (n + 1) ≤ ((p : ℝ)⁻¹) ^ n :=
            pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp.le) (Nat.le_succ n)
        _ ≤ ε := hn.le
  · rintro ⟨n, hn⟩
    have := congrFun hn ()
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact pow_ne_zero (n + 1) hp0 this.symm

example {Γ : Type} [Group Γ] (a : ℕ) : trc (1 : Γ →* GL (Fin a) ℚ) 1 = a := by
  simp [trc]

example {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (g : Γ) (v : V) :
    opOf ρ (Finsupp.single g 1) v = ρ g v := by
  simp [opOf]

end GlobalTheory.Cong

end
end

