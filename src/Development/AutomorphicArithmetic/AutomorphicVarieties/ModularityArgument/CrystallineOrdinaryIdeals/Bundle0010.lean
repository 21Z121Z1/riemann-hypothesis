import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleCrysAddAnn
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology TensorProduct

noncomputable section
namespace GlobalTheory.CrysAnn

variable {l : ℕ} [Fact l.Prime]

theorem actC_resCoef {G E B : Type} [Group G] [Field E] [Algebra ℚ_[l] E] [CommRing B] [Algebra ℚ_[l] B]
    [Algebra E B] [IsScalarTower ℚ_[l] E B] (φ : G →* GQ l) (ρ : Representation B G B) (g : G)
    (y : B ⊗[ℚ_[l]] Bcr l) : actC φ (resCoef E ρ) g y = actC φ ρ g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [actC, resCoef]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def smulRep {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] (N : Type) [AddCommGroup N]
    [Module B N] [Module E N] [IsScalarTower E B N] (χ : G →* Bˣ) : Representation E G N where
  toFun g := (LinearMap.lsmul B N (χ g : B)).restrictScalars E
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    simp [mul_smul]
    exact smul_comm _ _ _

end GlobalTheory.CrysAnn

open GlobalTheory.CrysAnn in

theorem GlobalTheory.CrysAnn.cocycle_crys_add_ann : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → ∀ c ∈ Z1 (chRep χ), ∃ c' : G → B, (∀ g, ((χ σ : B) - (cycA l l B (φ σ) : B)) * c' g = 0) ∧ c - c' ∈ finiteCocycles φ (chRep χ) ∧ (2 ≤ w → c' = 0) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI σ hσ c hc
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  set δ : B := if w = 1 then (χ σ : B) - (cycA l l B (φ σ) : B) else 1 with hδ
  have hspan : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E)) =
      Ideal.span {δ} := by
    have h := GlobalTheory.T.span_character_sub_cyclotomic_eq_of_positive_weight φ hφ π hπ χ hχc w hw hχI σ hσ
    have e : ∀ g, algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E) = (cycA l l B (φ g) : B) := fun g =>
      congrArg Units.val (algebraMap_cycA (E := E) (B := B) (φ g))
    simp only [e, h, hδ]
    split_ifs <;> simp
  let I : Submodule B B := LinearMap.ker (LinearMap.lsmul B B δ)
  letI : TopologicalSpace I := moduleTopology ℚ_[l] I
  haveI : IsModuleTopology ℚ_[l] I := ⟨rfl⟩
  haveI : IsTopologicalAddGroup I := IsModuleTopology.topologicalAddGroup ℚ_[l] I
  haveI : ContinuousConstSMul E I := ⟨fun a => IsModuleTopology.continuous_of_linearMap
    ((LinearMap.lsmul E I a).restrictScalars ℚ_[l])⟩
  haveI : FiniteDimensional ℚ_[l] I :=
    Module.Finite.of_injective (I.subtype.restrictScalars ℚ_[l]) Subtype.val_injective
  let ρV : Representation E G B := resCoef E (chRep χ)
  let ρW : Representation E G I := smulRep I χ
  have hV := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρV (fun g x => rfl)
  have hW := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρW (fun g x => rfl)
  have dV := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρV (fun g x => rfl) δ hspan
  have dW := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρW (fun g x => rfl) δ hspan
  have kW : LinearMap.ker ((LinearMap.lsmul B I δ).restrictScalars E) = ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subtype.ext x.2
  have hdim : finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρV) := by
    rw [dV, dW, kW, finrank_top]
    exact (LinearEquiv.refl E I).finrank_eq
  let i : I →ₗ[E] B := I.subtype.restrictScalars E
  obtain ⟨cW, -, hf⟩ := GlobalTheory.T.cocycle_mem_crystalline_sup_subrep_of_positive hP φ hφ ρW ρV hW.1 hV.1 hW.2 hV.2 i Subtype.val_injective
    (fun g x => rfl) hdim c hc
  have hz : w ≠ 1 → ∀ g, (cW g : B) = 0 := by
    intro h1 g
    have := (cW g).2
    simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_neg h1, one_smul] at this
    exact this
  refine ⟨fun g => (cW g : B), fun g => ?_, ?_, fun h2 => funext fun g => hz (by omega) g⟩
  · by_cases h1 : w = 1
    · have := (cW g).2
      simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_pos h1, smul_eq_mul] at this
      exact this
    · show _ * (cW g : B) = 0
      rw [hz h1 g, mul_zero]
  · obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hf
    exact ⟨⟨hc1, hc2⟩, x, fun g => (hx g).trans (by rw [actC_resCoef])⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriCrys
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tri_crys : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ finiteCocycles φ (chRep (κ 0 / κ 1)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → IsCr φ (colRep ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκ hI x y z ρ hz hρ hxf hyf
  have hxc : Continuous x := hxf.1.1
  have hyc : Continuous y := hyf.1.1
  have hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := fun g h => hxf.1.2 g h
  have crκ : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hI g hg i, smul_eq_mul]
  have hext : IsCr φ (ext2 (κ 0) (κ 1) x hx) :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ (κ 0) (κ 1) (hκ 0) (hκ 1) x hx hxc (crκ 0) (crκ 1)).2 hxf
  have hmat : ∀ g h (i j : Fin 3), (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i j =
      ((ρ g : Matrix (Fin 3) (Fin 3) B) * (ρ h : Matrix (Fin 3) (Fin 3) B)) i j := fun g h i j => by
    rw [map_mul, Units.val_mul]
  have hZ : (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
    refine ⟨hz.prodMk hyc, fun g h => ?_⟩
    have h02 := hmat g h 0 2
    have h12 := hmat g h 1 2
    rw [hρ, hρ, hρ] at h02 h12
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h02 h12

    have hu : ((κ 2 g : Bˣ) : B) * (((κ 2 g)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    have hv : ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    rw [twist_apply, characterExtensionRep_apply, MonoidHom.inv_apply]
    ext
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h02 - ((z (g * h) - z g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((z (g * h) - z g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 0 g : Bˣ) : B) * z h + x g * ((κ 1 g : Bˣ) : B) * y h)) * hv
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h12 - ((y (g * h) - y g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((y (g * h) - y g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 1 g : Bˣ) : B) * y h)) * hv
  exact (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ x y z ρ hxc hyc hz hρ hx hext (crκ 2)).2
    (GlobalTheory.T.ordinary_lift_local_iso hP φ hφ π hπ e he κ hκ hI x hx hxc hext y z hZ hyf)

end GlobalTheory
end

