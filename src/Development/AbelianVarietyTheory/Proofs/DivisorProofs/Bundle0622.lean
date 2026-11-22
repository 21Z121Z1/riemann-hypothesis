import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.ProdGalois
variable {S : Scheme.{0}}

theorem transl_lift_fst {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ fst A A = fst A A ≫ transl h₁ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_fst,
    ← Category.assoc, toUnit_unique (fst A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_snd {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ snd A A = snd A A ≫ transl h₂ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_snd,
    ← Category.assoc, toUnit_unique (snd A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_fst_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (fst A A).left = (fst A A).left ≫ (transl h₁).left := by
  rw [← Over.comp_left, transl_lift_fst, Over.comp_left]

theorem transl_lift_snd_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (snd A A).left = (snd A A).left ≫ (transl h₂).left := by
  rw [← Over.comp_left, transl_lift_snd, Over.comp_left]

theorem grpScheme_square_hom_ext_fst_snd {A : Over S} {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem grpSchemeSquareProductMap_eq_pullback_map {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = pullback.map A.hom A.hom A'.hom A'.hom ψ.left ψ.left (𝟙 S) (by simp) (by simp) := by
  apply grpScheme_square_hom_ext_fst_snd
  · rw [grpSchemeSquareProductMap_comp_fst]; exact (pullback.lift_fst _ _ _).symm
  · rw [grpSchemeSquareProductMap_comp_snd]; exact (pullback.lift_snd _ _ _).symm

end GlobalTheory.UPel.HT.Hecke.ProdGalois

open GlobalTheory.UPel.HT.Hecke.ProdGalois in

theorem GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  intro S A A' _ _ _ _ G ψ _ hψ
  have := hψ.finite
  have hfin := hψ.fin
  have het := hψ.etale
  have hon := hψ.onto
  refine
    { finite := inferInstance
      one := ?_
      mul := ?_
      inv := ?_
      fin := ?_
      etale := ?_
      onto := ?_
      fibre := ?_ }
  · apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).1 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
    · rw [transl_lift_snd_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).2 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
  · intro a c
    apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.assoc, transl_lift_fst_left, reassoc_of% transl_lift_fst_left]
      have e := hψ.mul a.1 c.1
      rw [show ((a * c).1 : 𝟙_ (Over S) ⟶ A) = ((a.1 * c.1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
    · rw [transl_lift_snd_left, Category.assoc, transl_lift_snd_left, reassoc_of% transl_lift_snd_left]
      have e := hψ.mul a.2 c.2
      rw [show ((a * c).2 : 𝟙_ (Over S) ⟶ A) = ((a.2 * c.2 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
  · intro a
    apply grpScheme_square_hom_ext_fst_snd
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, reassoc_of% transl_lift_fst_left, hψ.inv a.1]
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, reassoc_of% transl_lift_snd_left, hψ.inv a.2]
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    exact MorphismProperty.pullback_map (P := @IsFinite) hfin hfin (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Etale.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullback_map (P := @Etale) het het (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullback_map (P := @Surjective) hon hon (Over.w ψ).symm (Over.w ψ).symm
  · intro K _ _ y y' e
    have e₁ : (y ≫ (fst A A).left) ≫ ψ.left = (y' ≫ (fst A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_fst, reassoc_of% e]
    have e₂ : (y ≫ (snd A A).left) ≫ ψ.left = (y' ≫ (snd A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_snd, reassoc_of% e]
    obtain ⟨a₁, ha₁, hu₁⟩ := hψ.fibre K _ _ e₁
    obtain ⟨a₂, ha₂, hu₂⟩ := hψ.fibre K _ _ e₂
    refine ⟨(a₁, a₂), ?_, ?_⟩
    · apply grpScheme_square_hom_ext_fst_snd
      · rw [Category.assoc, transl_lift_fst_left, ← Category.assoc]; exact ha₁
      · rw [Category.assoc, transl_lift_snd_left, ← Category.assoc]; exact ha₂
    · intro b hb
      refine Prod.ext (hu₁ b.1 ?_) (hu₂ b.2 ?_)
      · show (y ≫ (fst A A).left) ≫ (transl (b.1 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (fst A A).left
        rw [Category.assoc, ← transl_lift_fst_left _ (b.2 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (fst A A).left) hb
      · show (y ≫ (snd A A).left) ≫ (transl (b.2 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (snd A A).left
        rw [Category.assoc, ← transl_lift_snd_left (b.1 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (snd A A).left) hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoLBCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixUniq

open GlobalTheory.HomFixMat

theorem psi_unique {Rg : Type} [CommRing Rg] {A : Over (Sp Rg)} [GrpObj A] {X : Scheme.{0}} (ψ ψ₂ : X ⟶ (topS Rg ⊗ A).left)
    (h : ψ ≫ (snd (topS Rg) A).left = ψ₂ ≫ (snd (topS Rg) A).left) : ψ = ψ₂ := by
  haveI : Mono (topS Rg).hom := by
    show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  have e : ψ ≫ (fst (topS Rg) A).left = ψ₂ ≫ (fst (topS Rg) A).left := by
    rw [← cancel_mono (topS Rg).hom]
    simp only [Category.assoc, Over.w]
    rw [← Over.w (snd (topS Rg) A), ← Category.assoc, h, Category.assoc]
  exact pullback.hom_ext e h

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]

variable (L : LB A.left) (M : LB B.left) in

def RigEq (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R]
    (t : Sp R ⟶ Sp Rg) {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) : Prop :=
  ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k

theorem isoLB_cover {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left}
    {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)}
    (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (x : A'.left) :
    ∃ p, x ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := by
  have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
  obtain ⟨iM, hiM⟩ := hc M hM ((((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)).base x)
  obtain ⟨iL, hiL⟩ := hc L hL (((ψA ≫ (snd (topS Rg) A).left)).base x)
  exact ⟨(fun _ => iM, fun _ => iL), Set.mem_iInter.2 fun _ => hiM, Set.mem_iInter.2 fun _ => hiL⟩

end GlobalTheory.HomFixUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimLEIsLocalRingQuotPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.LowBaseChange

theorem krullDimLE_isLocalRing_quot_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  have hJt : m ^ (n + 1) ≠ ⊤ := fun h => hm.ne_top
    (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 hJt
  have key : ∀ P : Ideal (R ⧸ m ^ (n + 1)), P.IsPrime →
      P = m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
    intro P hP
    have hc : (P.comap (Ideal.Quotient.mk (m ^ (n + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h1 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (n + 1))) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm.trans
      (congrArg _ (hm.eq_of_le hc.ne_top h1).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (R ⧸ m ^ (n + 1))
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ m ^ (n + 1))).out 1 0 rfl rfl).mp
    ⟨P, hP.isPrime, fun Q hQ => (key Q hQ).trans (key P hP.isPrime).symm⟩

variable {R : Type} [CommRing R]

theorem one_tmul_eq_zero_iff {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) (x : M) :
    (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R)
    (t : (R ⧸ I) ⊗[R] M) : ∃ x : M, (1 : R ⧸ I) ⊗ₜ[R] x = t :=
  TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective t

theorem projective_coker_of_approx [IsNoetherianRing R] {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (hyp : ∀ (m : Ideal R) [m.IsMaximal] (n : ℕ) (a : A), f a ∈ m • (⊤ : Submodule R B) →
      ∃ y : A, f y ∈ m ^ (n + 1) • (⊤ : Submodule R B) ∧ f a - f y ∈ m • LinearMap.range f) :
    Module.Projective R (B ⧸ LinearMap.range f) := by
  haveI : IsNoetherian R B := isNoetherian_of_isNoetherianRing_of_finite R B
  have hinjq : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor (R ⧸ m)) := by
    intro m _
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨⟨_, a, rfl⟩, rfl⟩ := exists_one_tmul m t
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, one_tmul_eq_zero_iff] at ht
    set N := B ⧸ (m • LinearMap.range f)
    have hq : (m • LinearMap.range f).mkQ (f a) ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R N) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨y, hy, hay⟩ := hyp m n a ht
      have e : (m • LinearMap.range f).mkQ (f a) = (m • LinearMap.range f).mkQ (f y) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]; exact hay
      rw [e]
      have hle : m ^ (n + 1) • (⊤ : Submodule R B) ≤
          (m ^ n • (⊤ : Submodule R N)).comap (m • LinearMap.range f).mkQ := by
        refine Submodule.smul_le.2 fun r hr x _ => ?_
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) hr) Submodule.mem_top
      exact hle hy
    obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff _).1 hq
    have h1 : f a - (r : R) • f a ∈ m • LinearMap.range f := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul]
      exact hr.symm
    have hsplit : (⟨f a, LinearMap.mem_range_self f a⟩ : LinearMap.range f) =
        ⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a) (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ +
          (r : R) • ⟨f a, LinearMap.mem_range_self f a⟩ := by
      ext; simp
    rw [hsplit, TensorProduct.tmul_add, ← TensorProduct.smul_tmul]
    have h2 : (1 : R ⧸ m) ⊗ₜ[R] (⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a)
        (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ : LinearMap.range f) = 0 := by
      rw [one_tmul_eq_zero_iff, Submodule.mem_smul_top_iff]; exact h1
    rw [h2, zero_add, Algebra.smul_def, _root_.mul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 r.2, TensorProduct.zero_tmul]
  have hinj : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor m.ResidueField) := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have hL : RingHom.ker (algebraMap R (R ⧸ m)) = m := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    have := GlobalTheory.exact_lTensor_iff_residueField m (R ⧸ m) hL
      (0 : PUnit →ₗ[R] LinearMap.range f) (LinearMap.range f).subtype
    rw [LinearMap.lTensor_zero, LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective,
      LinearMap.exact_zero_iff_injective] at this
    exact this.1 (hinjq m)
  obtain ⟨l, hl⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective
    (LinearMap.range f).subtype hinj
  have hex := (Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range f))
    Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
  obtain ⟨s, hs⟩ := hex.2 ⟨l, hl⟩
  exact Module.Projective.of_split s _ hs

end GlobalTheory.AbCoh.LowBaseChange

open GlobalTheory.AbCoh.LowBaseChange in

theorem GlobalTheory.AbCoh.projective_coker_of_liftsAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) →
      (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R']
        (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) →
      ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by
  intro R _ _ K hK _ hL i hi
  haveI := (hK (i + 1)).1
  haveI := (hK (i + 1)).2
  refine projective_coker_of_approx (K.d i (i + 1)).hom ?_
  intro m _ n a ha
  obtain ⟨h0, h1⟩ := krullDimLE_isLocalRing_quot_pow m n
  haveI := h1
  haveI : IsArtinianRing (R ⧸ m ^ (n + 1)) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, h0⟩
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hle : m ^ (n + 1) ≤ m := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let α : (R ⧸ m ^ (n + 1)) →ₐ[R] (R ⧸ m) := Ideal.Quotient.factorₐ R hle
  have hα : Function.Surjective α := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have hz : dB K (R ⧸ m) i (i + 1) ((1 : R ⧸ m) ⊗ₜ[R] a) = 0 := by
    rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff]
    exact ha
  obtain ⟨y, b, hy, hyb⟩ := hL i hi (R ⧸ m ^ (n + 1)) (R ⧸ m) α hα _ hz
  obtain ⟨y₀, rfl⟩ := exists_one_tmul _ y
  obtain ⟨b₀, rfl⟩ := exists_one_tmul _ b
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hy
  refine ⟨y₀, hy, ?_⟩
  rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    ← TensorProduct.tmul_add] at hyb
  have hdd : (K.d i (i + 1)).hom ((K.d (i - 1) i).hom b₀) = 0 := by
    have := congrArg (fun g => g.hom b₀) (K.d_comp_d (i - 1) i (i + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using this
  have hm : a - (y₀ + (K.d (i - 1) i).hom b₀) ∈ m • (⊤ : Submodule R (K.X i)) := by
    rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, ← hyb, sub_self]
  have := Submodule.mem_map_of_mem (f := (K.d i (i + 1)).hom) hm
  rw [Submodule.map_smul'', ← LinearMap.range_eq_map, map_sub, map_add, hdd, add_zero] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionRes
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

noncomputable section

namespace GlobalTheory.EtC.KumPic

section
variable (q : ℕ) [NeZero q]

theorem prim_pow_eq_one {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hr
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

def primUnit {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q (prim_pow_eq_one q ζ) (NeZero.ne q)

theorem primUnit_val {A : Type} [CommRing A] (ζ : Prim q A) : ((primUnit q ζ : Aˣ) : A) = ζ.1 :=
  Units.val_ofPowEqOne _ _ _ _

theorem dv_res (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤)))
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dv q φ U v) = dv q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold dv
  rw [show ∀ a b : Sec ((res ℤ (twZ q)).X 0) U, Sec.res g (a - b) = Sec.res g a - Sec.res g b from
    fun a b => LinearMap.map_sub _ a b, PicSpec.sec_map_res, PicSpec.unitSec_res, (restrMap _ _).nat, (kumT_spec q).1 V U g v hq]

variable (κ : twZ q ⟶ Gm)
  (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
    Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u)
  (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (hφ : κ ≫ φ = resι ℤ (twZ q))
include hκ hφ

theorem dv_mul_prim {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) :
    dv q φ U w = dv q φ U v := by
  have hu := primUnit_val q ζ
  have hw : w = primUnit q ζ * v := Units.ext (by rw [Units.val_mul, hu, h])
  have hk := (kumT_spec q).2 U ζ v w h
  have h1 : Sec.map φ (unitSec (primUnit q ζ)) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) := by
    rw [← hκ U ζ _ hu, PicSpec.sec_map_comp, hφ]
  have h2 : (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (resGen 1 ζ) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) :=
    restrMap_spec _ _ U _
  unfold dv
  rw [hk, map_add, h2, hw, PicSpec.unitSec_mul, PicSpec.sec_map_add, h1]
  abel

theorem dv_mul_prim_pow {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v → dv q φ U w = dv q φ U v := by
  induction a with
  | zero =>
    intro v w h
    rw [pow_zero, one_mul] at h
    rw [Units.ext h]
  | succ a ih =>
    intro v w h
    have h1 : ((primUnit q ζ ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, primUnit_val]
    rw [dv_mul_prim q κ hκ φ hφ ζ (primUnit q ζ ^ a * v) w (by rw [h, h1, pow_succ', mul_assoc]), ih v (primUnit q ζ ^ a * v) h1]

end

theorem dv_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  intro q _ κ hκ φ hφ U hq v v' hvv
  have sep := fun W : Scheme.{0} => (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ ((res ℤ (twZ q)).X 0) W).1
  apply sep U
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  rw [dv_res q φ g hq, dv_res q φ g hq]
  set x := Units.map g.appTop.hom.toMonoidHom v
  set x' := Units.map g.appTop.hom.toMonoidHom v'
  have hx : x ^ q = x' ^ q := by simp only [x, x', ← map_pow, hvv]
  apply sep V
  have hω : ((x' * x⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hx, inv_pow, mul_inv_cancel, Units.val_one]
  obtain ⟨S₂, hS₂, hP₂⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ _ hω
  refine ⟨S₂, hS₂, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP₂ W h hh
  rw [dv_res q φ h hqV, dv_res q φ h hqV]
  symm
  apply dv_mul_prim_pow q κ hκ φ hφ (ζ.map h.appTop.hom) a
  change h.appTop.hom (x' : Γ(V, ⊤)) = (h.appTop.hom ζ.1) ^ a * h.appTop.hom (x : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.EtC.KumPic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (i : ℤ), Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective) | (exact GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective) | (intros; apply GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerColumnCharacterEigenVecMulNeBotStatement
section
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviWhittakerColumnCharacter_eigen_vecMul_ne_bot : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (l : Fin r → F) (h : blockTri (κ := F) b), (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) → eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ → eig σ (colSet F b k.val) (colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot | exact GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransfer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullIsoCongr

theorem lbIso_pull_congr (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X) (h₁ : Q₁.IsLB) (h₂ : Q₂.IsLB)
    (e : LBIso Q₁ Q₂) (f : LBIso (Q₁.pull m) (Q₁.pull m')) : LBIso (Q₂.pull m) (Q₂.pull m') := by
  have a : LBIso (Q₂.pull m) (Q₁.pull m) :=
    LBIso.chartPull (chartPullPull Q₂ m m rfl) (chartPullPull Q₁ m m rfl) (LBIso.symm e)
  have b : LBIso (Q₁.pull m') (Q₂.pull m') :=
    LBIso.chartPull (chartPullPull Q₁ m' m' rfl) (chartPullPull Q₂ m' m' rfl) e
  exact LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m') (pull_isLB h₂ m')
    (LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m) (pull_isLB h₁ m') a f) b

theorem isocongr : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') :=
  fun X Y Q₁ Q₂ m m' h₁ h₂ e f => lbIso_pull_congr X Y Q₁ Q₂ m m' h₁ h₂ e f

end GlobalTheory.PullIsoCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosetsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets : ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) → (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) → {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x → ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  first | exact @GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul | exact GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul | (intros; apply GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul <;> assumption)
end

