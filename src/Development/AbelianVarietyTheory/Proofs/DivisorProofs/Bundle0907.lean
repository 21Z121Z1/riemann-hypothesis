import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusTangentVectorsAddMonoidHom
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
section
attribute [local instance] Over.cartesianMonoidalCategory
namespace TorusTangent

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

def epsUnit (a : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr a
  inv := 1 - TrivSqZeroExt.inr a
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem epsUnit_add (a b : k) : epsUnit (a + b) = epsUnit a * epsUnit b := by
  ext <;> simp [epsUnit, add_comm]

theorem natur {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) := by
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  exact (congrArg (fun g => g.hom x) this).symm

noncomputable def phi (l : X →+ k) : Multiplicative X →* Γ((epsPt (𝟙 (Sp k))).left, ⊤)ˣ :=
  (Units.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom.toMonoidHom).comp
    { toFun := fun χ => epsUnit (l χ.toAdd)
      map_one' := by ext <;> simp [epsUnit]
      map_mul' := fun a b => by rw [toAdd_mul, map_add, epsUnit_add] }

noncomputable def tanPt (l : X →+ k) : epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X :=
  (splitTorusPointsEquiv (Sp k) X (epsPt (𝟙 (Sp k)))).symm (phi l)

theorem chV_tanPt (l : X →+ k) (χ : X) :
    (chV (tanPt l) χ).val = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
      (1 + TrivSqZeroExt.inr (l χ)) := by
  show ((splitTorusPointsEquiv _ _ _) ((splitTorusPointsEquiv _ _ _).symm (phi l))
    (Multiplicative.ofAdd χ)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem chV_comp {Z Z' : Over (Sp k)} (j : Z' ⟶ Z) (t : Z ⟶ splitTorus (Sp k) X) (χ : X) :
    (chV (j ≫ t) χ).val = j.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem ext_val {Z : Over (Sp k)} {a b : Z ⟶ splitTorus (Sp k) X}
    (h : ∀ χ, (chV a χ).val = (chV b χ).val) : a = b :=
  TorusOfCharMap.ext_chV fun χ => Units.ext (h χ)

end TorusTangent
end

open TorusTangent in

theorem splitTorus_tangent_addHom : ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X], ∃ U : (X →+ k) → (epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ (τ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X) (ρ : X →+ X), (∀ χ, chV τ χ = charUnit (Sp k) X (ρ χ)) → ∀ l, U l ≫ τ = U (l.comp ρ) := by
  intro k _ X _
  have hΓ := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm.injective
  refine ⟨tanPt, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    ext χ
    have e := congrArg (fun t => (chV t χ).val) h
    simp only [chV_tanPt] at e
    have e2 := congrArg TrivSqZeroExt.snd (hΓ e)
    simpa using e2
  · intro l
    let j : Over.mk (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1)
    have : j ≫ tanPt l = 1 := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt]
      simp only [j, Over.homMk_left]
      rw [natur]
      simp [chV, map_one]
    exact congrArg CommaMorphism.left this
  · intro l l'
    show (splitTorusPointsEquiv _ _ _).symm _ =
      (splitTorusPointsEquiv _ _ _).symm (phi l) * (splitTorusPointsEquiv _ _ _).symm (phi l')
    rw [← map_mul]
    congr 1
    ext χ
    simp [phi, epsUnit_add]
  · intro t l
    let s : epsPt (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (epsScale t)) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change epsScale t (algebraMap k (DualNumber k) x) = algebraMap k (DualNumber k) x
        ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl])
    have : tanPt ((AddMonoidHom.mulLeft t).comp l) = s ≫ tanPt l := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt, chV_tanPt]
      simp only [s, Over.homMk_left]
      rw [natur]
      congr 1
      ext <;> simp [epsScale, mul_comm]
    rw [this]
    rfl
  · intro τ ρ hτ l
    have hm := ((splitTorus_map_of_charHom (Sp k) X X ρ).2 τ hτ).2.2
    refine ext_val fun χ => ?_
    rw [hm, chV_tanPt, chV_tanPt]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSL2Adeles
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.StrongApproximationSL2

section General

variable {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) (ε : R)

def prodMonoid : Submonoid (Matrix (Fin 2) (Fin 2) R) where
  carrier := {x | ∃ γ : Matrix (Fin 2) (Fin 2) K, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) R,
    h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map φ * h}
  one_mem' := ⟨1, by simp, 1, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨γ, hγ, h, hh, hε, rfl⟩ ⟨γ', hγ', h', hh', hε', rfl⟩
    set G := γ'.map φ with hG
    have hGd : G.det = 1 := by
      rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ', map_one]
    have h1 : G * G.adjugate = 1 := by rw [Matrix.mul_adjugate, hGd, one_smul]
    have h2 : G.adjugate * G = 1 := by rw [Matrix.adjugate_mul, hGd, one_smul]
    have h3 : G.adjugate.det = 1 := by
      have := congrArg Matrix.det h1
      rwa [det_mul, hGd, one_mul, det_one] at this
    refine ⟨γ * γ', by rw [det_mul, hγ, hγ', one_mul], G.adjugate * h * G * h', ?_, ?_, ?_⟩
    · rw [det_mul, det_mul, det_mul, h3, hh, hGd, hh']; simp
    · have e : G.adjugate * h * G * h' - 1 = G.adjugate * (h - 1) * G * h' + (h' - 1) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2, Matrix.sub_mul, Matrix.one_mul]
        abel
      rw [e, smul_add, hε', ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.mul_smul, hε]
    · rw [Matrix.map_mul, ← hG]
      calc γ.map φ * h * (G * h') = γ.map φ * (G * G.adjugate) * h * (G * h') := by rw [h1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]

theorem upper_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, φ t + ε * s; 0, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, t; 0, 1], by simp [det_fin_two], !![1, ε * s; 0, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lower_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, 0; φ t + ε * s, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, 0; t, 1], by simp [det_fin_two], !![1, 0; ε * s, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem mem_of_elementary (M : Submonoid (Matrix (Fin 2) (Fin 2) R)) (hU : ∀ x : R, !![1, x; 0, 1] ∈ M)
    (hL : ∀ x : R, !![1, 0; x, 1] ∈ M) (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R)
    (hu : (g 1 0 + g 1 1 * s) * u = 1) : g ∈ M := by
  rw [det_fin_two] at hg
  have e : g = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
      !![1, (g 1 1 - 1) * u; 0, 1] * !![1, 0; -s, 1] := by
    have e1 : g * !![1, 0; s, 1] = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
        !![1, (g 1 1 - 1) * u; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination (-(g 0 0 + g 0 1 * s - 1)) * hu
      · linear_combination (-(g 0 1) - (g 0 0 + g 0 1 * s - 1) * (g 1 1 - 1) * u) * hu - u * hg
      · linear_combination (-(g 1 1 - 1)) * hu
    have e2 : (!![1, 0; s, 1] * !![1, 0; -s, 1] : Matrix (Fin 2) (Fin 2) R) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← e1, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [e]
  exact M.mul_mem (M.mul_mem (M.mul_mem (hU _) (hL _)) (hU _)) (hL _)

theorem exists_unit_of_idem {c d a b : R} (haa : a * a = a) (hbb : b * b = b) (hab : a * b = 0) (hs : a + b = 1)
    (hw : IsUnit (a * c + b * d)) : ∃ s u : R, (c + d * s) * u = 1 := by
  obtain ⟨w, hw⟩ := hw.exists_right_inv
  have h1 : a * c * w = a := by linear_combination a * hw - c * w * haa - d * w * hab
  have h2 : b * d * w = b := by linear_combination b * hw - d * w * hbb - c * w * hab
  refine ⟨b * (1 - c) * w, a * w + b, ?_⟩
  have h3 : c + d * (b * (1 - c) * w) = a * c + b := by linear_combination (1 - c) * h2 - c * hs
  rw [h3]
  linear_combination hs + h1 + hbb + (c + w) * hab + c * w * haa

theorem mem_closure_of_dense [TopologicalSpace R] [IsTopologicalRing R] (hε : ε * ε = ε)
    (hd : ∀ (x : R) (U : Set R), U ∈ 𝓝 x → ∃ t : K, ∃ s : R, φ t + ε * s ∈ U)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R) (hu : (g 1 0 + g 1 1 * s) * u = 1) :
    g ∈ closure (prodMonoid φ ε : Set (Matrix (Fin 2) (Fin 2) R)) := by
  have key : ∀ f : R → Matrix (Fin 2) (Fin 2) R, Continuous f → (∀ t s, f (φ t + ε * s) ∈ prodMonoid φ ε) →
      ∀ x, f x ∈ (prodMonoid φ ε).topologicalClosure := by
    intro f hf h x
    change f x ∈ closure _
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨t, s, hts⟩ := hd x _ (hf.continuousAt.preimage_mem_nhds hV)
    exact ⟨_, hts, h t s⟩
  refine mem_of_elementary (prodMonoid φ ε).topologicalClosure ?_ ?_ g hg s u hu
  · refine key (fun x => !![1, x; 0, 1]) ?_ (upper_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine key (fun x => !![1, 0; x, 1]) ?_ (lower_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end General

theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

theorem strongApprox_SL2 : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  intro F _ _ S₁ S₂ ε hε hS g hg
  have hdet : ∑ i : Fin 2, ![-g 0 1, g 0 0] i * g 1 i = 1 := by
    rw [det_fin_two] at hg
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hg
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 2) (g 1) ![-g 0 1, g 0 0] (hdet ▸ isUnit_one)
  rw [Fin.sum_univ_two] at h3 h4
  obtain ⟨s, u, hu⟩ := exists_unit_of_idem (h1 0) (h1 1) (h2 0 1 (by decide)) h3 h4
  refine mem_closure_of_dense (algebraMap F (AF F)) ε (idem_of_isPlacesIdem hε) (fun x U hU => ?_) g hg s u hu
  obtain ⟨t, -, s, h⟩ := GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x U hU ∅
  exact ⟨t, s, h⟩

end GlobalTheory.StrongApproximationSL2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevelStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_mem_smul_top_of_neat_level_alt : ∀ (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La), Module.Finite (𝓞 E) Λ → Module.IsTorsionFree (𝓞 E) Λ → 0 < n → (n : 𝓞 E) ∈ J → (∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) → (∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q) → (∀ b, ψ b = 0 ↔ ∃ b', b = n • b') → (∀ q : Q, n • q = 0 → ∃ b, ψ b = q) → (∀ b, ψ (F b) = θ (ψ b)) → (∀ a, θ (ev (gM a)) = ev a) → 0 < N → F ^ N = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → J ≤ I₁ → J ≤ I₂ → (∀ x, ((gM - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) La)) → (∀ x, ((gM - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) La)) → ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by
  first | exact @GlobalTheory.sub_mem_smul_top_of_neat_level | exact GlobalTheory.sub_mem_smul_top_of_neat_level | (intros; apply GlobalTheory.sub_mem_smul_top_of_neat_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsetOfForallPtMem
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Adelic

theorem subset_of_forall_pt_mem : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → ∀ (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (Z : Set S.Y), IsClosed Z → ∀ U : Set S.Y, IsOpen U →
    (∀ x : S.Pt Ω, ptOf x.1 ∈ Z → ptOf x.1 ∈ U) → Z ⊆ U := by
  intro k _ S hS Ω _ _ _ Z hZ U hU h
  haveI := hS.smooth
  haveI : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  haveI : LocallyOfFiniteType S.str := inferInstance
  haveI : JacobsonSpace S.Y := LocallyOfFiniteType.jacobsonSpace S.str
  by_contra hne
  obtain ⟨z, hzZ, hzU⟩ := Set.not_subset.1 hne
  obtain ⟨y, ⟨hyZ, hyU⟩, hy⟩ := nonempty_inter_closedPoints (Z := Z ∩ Uᶜ) ⟨z, hzZ, hzU⟩
    (hZ.inter hU.isClosed_compl).isLocallyClosed
  have hyc : IsClosed ({y} : Set S.Y) := hy
  haveI : IsFinite (resPt y ≫ S.str) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hyc
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    unfold resPt
    infer_instance
  have hφ : (S.baseHom (resPt y)).IsIntegral := by
    have : IsIntegralHom (Spec.map (Spec.preimage (resPt y ≫ S.str))) := by
      rw [Spec.map_preimage]; infer_instance
    rw [IsIntegralHom.SpecMap_iff] at this
    exact this
  letI : Algebra k (S.Y.residueField y) := (S.baseHom (resPt y)).toAlgebra
  haveI : Algebra.IsIntegral k (S.Y.residueField y) := ⟨hφ⟩
  let τ : S.Y.residueField y →ₐ[k] Ω := IsAlgClosed.lift
  let x : S.Pt Ω := ⟨spMap τ.toRingHom ≫ resPt y, by
    rw [Category.assoc, S.comp_str, ← Spec.map_comp]
    congr 1
    ext a
    exact τ.commutes a⟩
  have hx : ptOf x.1 = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  exact hyU (hx ▸ h x (hx.symm ▸ hyZ))

end GlobalTheory.Adelic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverse
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.GeoActCompare.TameAB

variable {D : D7}

abbrev cFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  sigR (Af D.host.F) D.sp.cm.sig

theorem cFin_tmul (a : Af D.host.F) (e : D.host.E) :
    cFin D (a ⊗ₜ e) = a ⊗ₜ IsCMField.complexConj D.host.E e := rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = cFin D (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a e => rfl

theorem cFin_mem_intAE (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : cFin D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, H.bar x, by rw [cFin_tmul, H.bar_eq]⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem swapAE_mem {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) : swapAE D z ∈ LatticeBasisLifts.OAf D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, rfl⟩ := hw
    have h1 : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ LatticeBasisLifts.OAf D :=
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have h2 : (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F) ∈ LatticeBasisLifts.OAf D :=
      Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩)
    have := mul_mem h2 h1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    exact this
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem swapAE_idealHat {I : Ideal (𝓞 D.host.E)} {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ LevelLiftConditions.idealHat D I) :
    ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, ((s : LatticeBasisLifts.OAf D) : EAf D) = swapAE D z := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, y, hy, rfl⟩ := hw
    refine ⟨Formalism.L2.DIV.oToS D.host.F D.host.E b * ⟨_, swapAE_mem hy⟩,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), ?_⟩
    rw [RingHom.map_mul]
    rfl
  | zero => exact ⟨0, zero_mem _, by rw [RingHom.map_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, e⟩ := hx
    obtain ⟨t, ht, e'⟩ := hy
    exact ⟨s + t, add_mem hs ht, by rw [RingHom.map_add, ← e, ← e']; rfl⟩
  | neg x _ hx =>
    obtain ⟨s, hs, e⟩ := hx
    exact ⟨-s, neg_mem hs, by rw [RingHom.map_neg, ← e]; rfl⟩

theorem bar_bar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (a : 𝓞 D.host.E) : H.bar (H.bar a) = a :=
  Subtype.ext (by
    have h := H.bar_eq (H.bar a)
    rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h
    exact h)

theorem cFin_idealHat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {I : Ideal (𝓞 D.host.E)}
    {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ LevelLiftConditions.idealHat D (I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))) :
    cFin D z ∈ LevelLiftConditions.idealHat D I := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, y, hy, rfl⟩ := hw
    obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)
      H.bar.surjective).1 hb
    refine AddSubgroup.subset_closure ⟨c, hc, _, cFin_mem_intAE H hy, ?_⟩
    rw [RingHom.map_mul, cFin_tmul, ← H.bar_eq]
    exact congrArg (fun t : 𝓞 D.host.E => ((1 : Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E)) * cFin D y) (bar_bar H c)
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem exists_unit_subring {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (S : Subring B) (x : Aˣ)
    (h : f (x : A) ∈ S) (h' : f ((x⁻¹ : Aˣ) : A) ∈ S) : ∃ u : Sˣ, ((u : S) : B) = f (x : A) :=
  ⟨⟨⟨_, h⟩, ⟨_, h'⟩, Subtype.ext (by simp [← map_mul]), Subtype.ext (by simp [← map_mul])⟩, rfl⟩

theorem resS_eq_of_cong {I : Ideal (𝓞 D.host.E)} (w : Formalism.L2.DIV.Pl D.host.E) (hw : I ≤ w.asIdeal)
    (s : LatticeBasisLifts.OAf D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hs : (s : EAf D) = swapAE D z) (a : 𝓞 D.host.E)
    (hz : z - (1 : Af D.host.F) ⊗ₜ (a : D.host.E) ∈ LevelLiftConditions.idealHat D I) :
    Formalism.L2.DIV.resS D.host.F w s = Ideal.Quotient.mk w.asIdeal a := by
  obtain ⟨t, ht, e⟩ := swapAE_idealHat hz
  rw [resS_eq_resI, resI_eq_mk_iff]
  have : s - Formalism.L2.DIV.oToS D.host.F D.host.E a = t := by
    apply Subtype.ext
    rw [e, RingHom.map_sub, ← hs]
    rfl
  rw [this]
  exact Ideal.map_mono hw ht

theorem isInvTame_chiProd : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), LatticeBasisLifts.IsInvTame σ Pg μ χ → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) := by
  intro D H l Pg hle K _ σ μ χ h x hx u ub hub h1 h2
  obtain ⟨hinf, hi, hi'⟩ := hx
  obtain ⟨U, hU⟩ := exists_unit_subring ((swapAE D).comp (finPart D)) (LatticeBasisLifts.OAf D) x (swapAE_mem hi) (swapAE_mem hi')
  obtain ⟨Ub, hUb⟩ := exists_unit_subring ((swapAE D).comp ((cFin D).comp (finPart D))) (LatticeBasisLifts.OAf D) x
    (swapAE_mem (cFin_mem_intAE H hi)) (swapAE_mem (cFin_mem_intAE H hi'))
  have key := h x U Ub hinf hU (by rw [finPart_cA]; exact hUb)
  have e1 : ∀ w : ↥Pg, Units.map (Formalism.L2.DIV.resS D.host.F w.1).toMonoidHom U =
      Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom ub := fun w => Units.ext (by
    have := resS_eq_of_cong w.1 (hle w) U _ hU u h1
    refine this.trans ?_
    change _ = Ideal.Quotient.factor (hle w) (ub : 𝓞 D.host.E ⧸ l.Mb)
    rw [hub]
    rfl)
  have e2 : ∀ w : ↥Pg, Units.map (Formalism.L2.DIV.resS D.host.F w.1).toMonoidHom Ub = 1 := fun w => Units.ext (by
    have h3 := cFin_idealHat H h2
    rw [RingHom.map_sub, cFin_tmul, ← H.bar_eq, map_one] at h3
    exact resS_eq_of_cong w.1 (hle w) Ub _ hUb 1 h3)
  rw [key, chiProd_apply, Units.coe_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [e1, e2, map_one, Units.val_one, map_one, mul_one]
  exact mul_inv_cancel₀ ((map_ne_zero σ).2 (Units.ne_zero _))

end GlobalTheory.GeoActCompare.TameAB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanScalDecomp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieCoordMult

theorem tanScal_decomp : ∀ (O : Type) [Ring O] (F' : Type) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (act : OActN O G) (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (n a : ℕ) (T : (Fin n → R') → (epsPtR x ⟶ G)) (A : O → Matrix (Fin n) (Fin n) R') (emb : F' → O) (ω : F') (l : R') (χ : Fin a → F' → R'), Function.Injective T → (∀ v : epsPtR x ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → (∀ b c, T c ≫ act.act b = T (A b *ᵥ c)) → (∀ y : Fin n → R', A (emb ω) *ᵥ y = l • y → ∃ z : Fin a → Fin n → R', (∀ i c, A (emb c) *ᵥ z i = χ i c • z i) ∧ y = ∑ i, z i) → ∀ v : epsPtR x ⟶ G, IsTanScal act x (emb ω) l v → ∃ w : Fin a → (epsPtR x ⟶ G), (∀ i c, IsTanScal act x (emb c) (χ i c) (w i)) ∧ v = (List.ofFn w).prod := by
  intro O _ F' S G _ _ act R' _ x n a T A emb ω l χ hinj htan hadd hsc hact hdec v hv
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → R')), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ (b : O) (c : R') (w : epsPtR x ⟶ G), IsTanScal act x b c w ↔ ∃ y, A b *ᵥ y = c • y ∧ w = T y := by
    intro b c w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (htan w).1 h1
      refine ⟨y, hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2, hsc]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(htan _).2 ⟨y, rfl⟩, ?_⟩
      rw [hact, hy, hsc]
  obtain ⟨y, hy, rfl⟩ := (eig _ _ _).1 hv
  obtain ⟨z, hz, rfl⟩ := hdec y hy
  exact ⟨fun i => T (z i), fun i c => (eig _ _ _).2 ⟨z i, hz i c, rfl⟩, (Tsum a z).symm⟩

end GlobalTheory.LieCoordMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  first | exact @GlobalTheory.unifAt_correspond_of_cartesian | exact GlobalTheory.unifAt_correspond_of_cartesian | (intros; apply GlobalTheory.unifAt_correspond_of_cartesian <;> assumption)
end

