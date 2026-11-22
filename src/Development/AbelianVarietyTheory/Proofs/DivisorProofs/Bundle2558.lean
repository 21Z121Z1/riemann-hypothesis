import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0948
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isObU_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L C' _ F' L' n l u u' c hL hN hu hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hex : ∀ T, ∃ s : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) s := fun T =>
    GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ' hσ' using hex
  have hnat : ∀ T : C', (∀ y, l T (σ (n.G.obj T) y) = σ' T (extHom R₁ (coefHom n T) y)) ∧
      ∀ y, α.KerQ y → α.KerQ (extHom R₁ (coefHom n T) y) := fun T =>
    GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _)
      _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) (l T) (coefHom n T) (fun b => hL T b) _ _ (hσ _) (hσ' T)
  refine ⟨fun T T' a => Units.map (l T').toRingHom.toMonoidHom (v _ _ (n.G.map a)), σ', (extMap R₁ n).pullbackTwoCocycle z,
    ?_, hσ', ?_, ?_⟩
  · intro T T' a
    change L'.p T' (l T' _) = _
    rw [hL, hv, hu]
  · rw [hc]; rfl
  · intro T T' T'' a b
    obtain ⟨hk1, hk2⟩ := hz _ _ _ (n.G.map a) (n.G.map b)
    refine ⟨(hnat T'').2 _ hk1, ?_⟩
    change L'.ρ b (l T' _) * l T'' _ = (1 + σ' T'' (extHom R₁ (coefHom n T'') _)) * l T'' _
    rw [hN, ← map_mul, hk2, map_mul, map_add, map_one, (hnat T'').1, Functor.map_comp]
    rfl

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionUnique
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem mul_eq_zero_of_mem_map {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {x x' : B} (hx : x ∈ I.map (algebraMap R B)) (hx' : x' ∈ I.map (algebraMap R B)) : x * x' = 0 := by
  have h := Ideal.mul_mem_mul hx hx'
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  exact (Submodule.mem_bot _).1 h

theorem isSig_unique {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
    [Algebra R₀ R₁] (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (hσ' : α.IsSig p σ')
    (y : R₁ ⊗[R₀] B₀) : σ' y = σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

theorem isObU_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u c' → c = c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  have hσσ : ∀ T y, σ' T y = σ T y := fun T y ↦ isSig_unique α (L.p T) (L.surj T) (σ T) (σ' T) (hσ T) (hσ' T) y
  have hy : ∀ (T T' : C) (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F.obj T', α.KerQ y ∧
      σ T' y = (v' T T' a : L.B T') * ((v T T' a)⁻¹ : (L.B T')ˣ) - 1 := by
    intro T T' a
    refine (sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T')
      (σ T') (hσ T')).2.2.2 _ ((L.ker T' _).1 ?_)
    rw [map_sub, map_mul, hv', ← hv, ← map_mul, Units.mul_inv, map_one, sub_self]
  choose y hyK hyσ using hy
  rw [H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -y T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L.smooth T''
  haveI : Module.Flat R (L.B T'') := Algebra.Smooth.flat R _
  have nat := sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T')
    (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b) (L.nat b)
    (σ T') (σ T'') (hσ T') (hσ T'')
  have bas := sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
    (L.ker T'') (σ T'') (hσ T'')
  have em : ∀ x, mp (ext R₁ F) b x = extHom R₁ (mp F b) x := fun _ ↦ rfl
  simp only [d1_apply, Pi.sub_apply, map_neg, em]
  rw [← sub_eq_zero]
  apply sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
    (L.ker T'') (σ T'') (hσ T'')
  · have k1 := nat.2 _ (hyK T T' a)
    have k2 := hyK T T'' (a ≫ b)
    have k3 := hyK T' T'' b
    have k4 := (hz T T' T'' a b).1
    have k5 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at k1 k2 k3 k4 k5 ⊢
    simp only [map_sub, map_add, map_neg, k1, k2, k3, k4, k5]
    simp
  ·
    have e1 := (hz T T' T'' a b).2
    have e2 := (hz' T T' T'' a b).2
    rw [hσσ] at e2
    set P := σ T'' (extHom R₁ (mp F b) (y T T' a)) with hP
    set Q := σ T'' (y T' T'' b) with hQ
    set Y := σ T'' (y T T'' (a ≫ b)) with hY
    set Z := σ T'' (z.1 T T' T'' a b) with hZ
    set Z' := σ T'' (z'.1 T T' T'' a b) with hZ'
    have va : (v' T T' a : L.B T') = (1 + σ T' (y T T' a)) * (v T T' a : L.B T') := by
      rw [hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    have vb : (v' T' T'' b : L.B T'') = (1 + Q) * (v T' T'' b : L.B T'') := by
      rw [hQ, hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    have vab : (v' T T'' (a ≫ b) : L.B T'') = (1 + Y) * (v T T'' (a ≫ b) : L.B T'') := by
      rw [hY, hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    rw [va, vb, vab, map_mul, map_add, map_one, nat.1] at e2
    rw [← hP] at e2
    have mem : ∀ x, σ T'' x ∈ I.map (algebraMap R (L.B T'')) := bas.1
    have sq : ∀ x x', σ T'' x * σ T'' x' = 0 := fun x x' ↦ mul_eq_zero_of_mem_map hI (mem x) (mem x')
    have hPQ : P * Q = 0 := sq _ _
    have hPZ : P * Z = 0 := sq _ _
    have hQZ : Q * Z = 0 := sq _ _
    have hZY : Z' * Y = 0 := sq _ _
    have hV : (v T T'' (a ≫ b) : L.B T'') * ((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) = 1 := Units.mul_inv _
    simp only [map_sub, map_add, map_neg]
    rw [← hP, ← hQ, ← hY, ← hZ, ← hZ']
    have E : (1 + P) * (1 + Q) * (1 + Z) * (v T T'' (a ≫ b) : L.B T'') =
        (1 + Z') * (1 + Y) * (v T T'' (a ≫ b) : L.B T'') := by
      linear_combination e2 - (1 + P) * (1 + Q) * e1
    linear_combination -(((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) : L.B T'') * E
      + ((1 + P) * (1 + Q) * (1 + Z) - (1 + Z') * (1 + Y)) * hV + (1 + Z) * hPQ + hPZ + hQZ - hZY

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftOfObstructionEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

def unitOneSub {B : Type} [CommRing B] (w : B) (h : w * w = 0) : Bˣ where
  val := 1 - w
  inv := 1 + w
  val_inv := by linear_combination (-1 : B) * h
  inv_val := by linear_combination (-1 : B) * h

theorem unitOneSub_val {B : Type} [CommRing B] (w : B) (h : w * w = 0) : (unitOneSub w h : B) = 1 - w := rfl

theorem mul_eq_zero_of_mem {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {x y : B} (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

theorem lift_of_isObU_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u h
  obtain ⟨v, σ, z, hv, hσ, hz, hzv⟩ := h
  obtain ⟨f, hf⟩ := (H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm
  have hw : ∀ (T T' : C) (a : T ⟶ T'), σ T' (f T T' a) ∈ I.map (algebraMap R (L.B T')) := fun T T' a ↦
    (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (σ T') (hσ T')).1 _
  refine ⟨fun T T' a ↦ v T T' a * unitOneSub (σ T' (f T T' a)) (mul_eq_zero_of_mem hI (hw T T' a) (hw T T' a)),
    fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · have h0 : L.p T' (σ T' (f T T' a)) = 0 := (L.ker T' _).2 (hw T T' a)
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one, h0, sub_zero, mul_one, hv]
    exact mul_one _
  · have hnat := (GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b)
      (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b
    have hs : σ T'' (z.1 T T' T'' a b) = L.ρ b (σ T' (f T T' a)) - σ T'' (f T T'' (a ≫ b)) + σ T'' (f T' T'' b) := by
      rw [← e, d1_apply, map_add, map_sub, hnat]
      rfl
    have hx := hw T T' a
    have hρx : L.ρ b (σ T' (f T T' a)) ∈ I.map (algebraMap R (L.B T'')) := by
      rw [hnat]
      exact (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
        (L.ker T'') (σ T'') (hσ T'')).1 _
    have hW := hw T T'' (a ≫ b)
    have hy := hw T' T'' b
    set x := L.ρ b (σ T' (f T T' a)) with hxdef
    set W := σ T'' (f T T'' (a ≫ b))
    set y := σ T'' (f T' T'' b)
    have hxx := mul_eq_zero_of_mem hI hρx hρx
    have hxy := mul_eq_zero_of_mem hI hρx hy
    have hyy := mul_eq_zero_of_mem hI hy hy
    have hWx := mul_eq_zero_of_mem hI hW hρx
    have hWy := mul_eq_zero_of_mem hI hW hy
    have key : (1 + (x - W + y)) * ((1 - x) * (1 - y)) = 1 - W := by
      linear_combination -hxx - hxy - hyy + hWx + hWy + y * hxx - y * hWx + y * hxy
    have hz' := (hzv T T' T'' a b).2
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one]
    rw [← hxdef]
    linear_combination (-(1 - x) * (1 - y)) * hz' + (-(v T T'' (a ≫ b) : L.B T'') * (1 - x) * (1 - y)) * hs
      - (v T T'' (a ≫ b) : L.B T'') * key

end GlobalTheory.LBLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroups
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_identity_unconditional :
    ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
      (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ :=
  GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie (GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis GlobalTheory.T.jacquetRallisUnitMatch_all_ranks).1

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelVacuum
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem frameMajorant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ A : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc → ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧
        ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N m t ξ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y hxy M₁ blk e hG hco hev Cc hCc c hc φ hφ
  obtain ⟨ex, hex⟩ := GlobalTheory.T.pair_frame_block_eigen_relation hKP F E σ B n d X W M χX χW om r s r' s' hP q x y hxy M₁ blk e hG hco hev φ hφ
  obtain ⟨A, hAex⟩ : ∃ A : ℕ, ∀ i, ex i ≤ A := by
    obtain ⟨A, hA⟩ := exists_nat_ge (∑ i, |ex i|)
    exact ⟨A, fun i => (le_abs_self _).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (ex j)) (Finset.mem_univ i)).trans hA)⟩
  refine ⟨A, fun N => ?_⟩
  obtain ⟨Cb, k, hb⟩ := GlobalTheory.T.evaluation_compact_set_bound hKP F E σ B n d X W M χX χW om r s r' s' hP M₁ e hG hev Cc hCc φ hφ ((q + 1) * N)
  obtain ⟨Cm, hCm0, hCm⟩ := GlobalTheory.T.block_scaled_norm_decay F blk hco.1 c hc N
  set Ct : ℝ := ∏ i, c ^ (ex i - A) with hCt
  have hCt0 : 0 ≤ Ct := Finset.prod_nonneg fun i _ => Real.rpow_nonneg hc.le _
  refine ⟨Cb * max 1 (Ct * Cm), k, ?_⟩
  intro f t a κ h htc ha hκ
  have ht0 : ∀ i, 0 < t i := fun i => hc.trans_le (htc i)
  obtain ⟨m, hm1, hmC, hz⟩ := hb f κ h hκ
  have hhk : 0 ≤ (ht h : ℝ) ^ k := pow_nonneg (NNReal.coe_nonneg _) _
  have hCb : 0 < Cb := by
    by_contra hneg
    push_neg at hneg
    have h2 : Cb * (ht h : ℝ) ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hhk
    have h3 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hmax : 1 ≤ max 1 (Ct * Cm) := le_max_left _ _
  refine ⟨m, hm1, hmC.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCb.le hmax) hhk), fun ξ => ?_⟩
  set z : Fin n × Fin d → AF F := fun j => algebraMap F (AF F) (ξ j) with hzdef
  have h1 := hex t a ht0 ha f κ h z
  have hp : 0 ≤ semK (Fin n × Fin d) k f := apply_nonneg _ _
  by_cases hI : ∀ j, IsIntegral ℤ ((m : F) * ξ j)
  · rw [majI, if_pos hI]
    obtain ⟨hbd, -⟩ := hz (blkScale blk t z)
    have hc' := hCm t htc ξ
    have hprod : (∏ i, t i ^ ex i) ≤ Ct * (∏ i, t i) ^ A := by
      rw [hCt, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (ht0 i).le _) (fun i _ => ?_)
      have e1 : t i ^ ex i = t i ^ (ex i - A) * t i ^ (A : ℝ) := by
        rw [← Real.rpow_add (ht0 i)]; ring_nf
      rw [e1, Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hc (htc i) (by linarith [hAex i])) (pow_nonneg (ht0 i).le _)
    have hW := majW_nonneg blk A N t ξ (fun i => (ht0 i).le)
    have hT : 0 ≤ (∏ i, t i) ^ A := pow_nonneg (Finset.prod_nonneg fun i _ => (ht0 i).le) _
    calc _ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := h1
      _ ≤ (Ct * (∏ i, t i) ^ A) * (Cb * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k *
            ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t z j))) ^ ((q + 1) * N))⁻¹) :=
          mul_le_mul hprod hbd (norm_nonneg _) (mul_nonneg hCt0 hT)
      _ ≤ (Ct * (∏ i, t i) ^ A) * (Cb * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k *
            (Cm * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
              (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc' ?_) (mul_nonneg hCt0 hT)
          exact mul_nonneg (mul_nonneg hCb.le hp) hhk
      _ = Cb * (Ct * Cm) * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majW blk A N t ξ := by
          unfold majW; ring
      _ ≤ Cb * max 1 (Ct * Cm) * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majW blk A N t ξ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hCb.le) hp) hhk) hW
  · have h0 : e (om (κ, h) (pureA F f φ)) (blkScale blk t z) = 0 := by
      by_contra hne
      exact hI fun j => GlobalTheory.T.block_scaled_integral_of_local F blk t m ξ j fun v => (hz _).2 hne j v
    rw [majI, if_neg hI, mul_zero]
    rw [h0, norm_zero, mul_zero] at h1
    exact h1

end GlobalTheory.ThKTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_points_deep_level : Hypotheses2 → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → UnramPts Y.d.Xo₂ Y.d.c₂ (badPrimes T.Q.H Y.d.l₂) := by
  first | exact @GlobalTheory.UnramCover.unramPts_deep | exact GlobalTheory.UnramCover.unramPts_deep | (intros; apply GlobalTheory.UnramCover.unramPts_deep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtUnique
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_unique {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ)
    (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (p : (torsion G n).left) (c c' : M) (h : GlobalTheory.TorsSpec.ValAt G n ℓ w p c)
    (h' : GlobalTheory.TorsSpec.ValAt G n ℓ w p c') : c = c' := by
  haveI : Etale (torsion G n).hom := GrpTangent.etale_torsion G hn
  obtain ⟨t, ht, e⟩ := Flat.generalizingMap (torsion G n).hom
    (genericPoint_specializes ((torsion G n).hom p))
  obtain ⟨q, rfl⟩ : t ∈ Set.range ((torsion G n).left.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact ht
  let D := Spec ((torsion G n).left.presheaf.stalk p)
  let y : Sp (AlgebraicClosure (D.residueField q)) ⟶ D :=
    Spec.map (CommRingCat.ofHom (algebraMap (D.residueField q) (AlgebraicClosure (D.residueField q)))) ≫
      D.fromSpecResidueField q
  let g := y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).mpr ⟨ℓ v, Set.mem_univ _, v, rfl⟩
  have hg : Set.range g ⊆ Set.range ℓ := by
    rintro _ ⟨a, rfl⟩
    have hya : y a = q := by
      have : y a ∈ Set.range (D.fromSpecResidueField q) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have : g a = (torsion G n).hom ((torsion G n).left.fromSpecStalk p (y a)) := rfl
    rw [this, hya, e]
    exact hgen
  let z := IsOpenImmersion.lift ℓ g hg
  have hz : z ≫ ℓ = g := IsOpenImmersion.lift_fac ℓ g hg
  have h1 := h _ y z hz.symm
  have h2 := h' _ y z hz.symm
  exact hun _ z c c' (h1.symm.trans h2)

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVwProdLe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.CovTop
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.CovHt.HTDiag

def LatBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : Host E), letI := H.starRing;
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]]
    (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p])
    (P : Point p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left),
    (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) →
    ∀ (τ : E →+* ℂ) (w : P.V), w ∈ htLat c P τ →
      w ∈ Submodule.span ℂ_[p] (P.wRec (embInt c P.integers τ) : Set P.V) →
      ∀ a : ℂ_[p], ‖a‖ ≤ (p : ℝ) ^ (-htEx E p) → a • w ∈ P.wRec (embInt c P.integers τ)

def DiagBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (T : CDVR) (io : c.F →+* T.Fr)
    (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y z : FrPt Xo c ℂ_[p]),
    IsHTFrameCp p y₀ k y → (letI := io.toAlgebra; FrMap k y₀.1 z) →
    ∃ t : Ix Dw → ℂ_[p]ˣ, FrBor t z y ∧ ‖(t none : ℂ_[p])‖ = 1 ∧
      ∀ s, 1 ≤ ‖(t (some s) : ℂ_[p])‖ ∧ ‖(t (some s) : ℂ_[p])‖ ≤ (p : ℝ) ^ htEx E p

end GlobalTheory.CovHt.HTDiag

namespace GlobalTheory.CovHt.HTDiag

theorem val_vw_prod_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (t : Ix Dw → ℂ_[p]ˣ) (ex : Ix Dw → ℤ) (h : ℝ) (h0 : ex none = 0)
    (ht : ∀ s, 1 ≤ ‖(t (some s) : ℂ_[p])‖ ∧ ‖(t (some s) : ℂ_[p])‖ ≤ (p : ℝ) ^ h) (he : 0 ≤ (vLa la (p : K) : ℝ))
    (hh : 0 ≤ h) :
    val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) ((∏ i, t i ^ ex i : ℂ_[p]ˣ) : ℂ_[p]) ≤
      (((vLa la (p : K) : ℝ) * h * ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |(ex (some s) : ℝ)| : ℝ) : EReal) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  rw [val_vw_of_ne la p _ (Units.ne_zero _), EReal.coe_le_coe_iff,
    GlobalTheory.PadicComplexHost.valuation_coe_eq_norm, GlobalTheory.PadicComplexHost.valuation_coe_eq_norm,
    GlobalTheory.PadicComplexHost.norm_p, Real.log_inv, Units.coe_prod, norm_prod, Real.log_prod]
  · simp only [Units.val_zpow_eq_zpow_val, norm_zpow, Real.log_zpow, Fintype.sum_option, h0, Int.cast_zero, zero_mul,
      zero_add]
    rw [_root_.mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ he
    rw [div_neg, ← neg_div, ← Finset.sum_neg_distrib, div_le_iff₀ hlp, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    obtain ⟨h1, h2⟩ := ht s
    have hl0 : 0 ≤ Real.log ‖(t (some s) : ℂ_[p])‖ := Real.log_nonneg h1
    have hl1 : Real.log ‖(t (some s) : ℂ_[p])‖ ≤ h * Real.log p := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) h2
    have := neg_abs_le (ex (some s) : ℝ)
    nlinarith [abs_nonneg (ex (some s) : ℝ)]
  · intro i _
    exact norm_ne_zero_iff.2 (t i ^ ex i).ne_zero

end GlobalTheory.CovHt.HTDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuativeExistence_of_dvr_lifts_locallyNoetherian : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  first | exact @GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing | exact GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing | (intros; apply GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_weightSection_flagSpace_eq_rule_at_framedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  first | exact @GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | exact GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | (intros; apply GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR <;> assumption)
end

