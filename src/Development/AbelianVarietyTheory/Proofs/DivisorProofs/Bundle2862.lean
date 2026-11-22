import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionCrossRelationIffOfThetaAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.CrossTheta₂

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} (p : Y' ⟶ X) {k : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k))) (r : Z ⟶ Y) (c : Y ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} {I : (Y ⟶ X) → L.ι} (hI : Good L (r z) I) (hc : I (c ≫ p) = J (r ≫ c ≫ p)) :
    sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
  rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
  exact GlobalTheory.CrossTheta.gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _

theorem cross_val {X₁ X₂ Y₁ Y₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂) (b : Y₁ ⟶ Y₂) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L₂ (fun _ : Fin 1 => p₂) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L₁ (fun _ : Fin 1 => p₁) (fun _ => k')))
    (H : ∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval s₁ b y J₂ * sval s₂' (𝟙 _) y J₁ = sval s₂ b y J₂ * sval s₁' (𝟙 _) y J₁)
    {Z : Scheme.{0}} (r : Z ⟶ Y₁) (z : Z) {J₁ J₂} (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    sval s₁ (r ≫ b) z J₂ * sval s₂' r z J₁ = sval s₂ (r ≫ b) z J₂ * sval s₁' r z J₁ := by
  obtain ⟨I₁, hI₁, e₁⟩ := exists_good L₁ hL₁ (r z) (K := Unit) (fun _ => 𝟙 _ ≫ p₁)
    (fun _ => J₁ (r ≫ 𝟙 _ ≫ p₁)) (fun _ _ _ => rfl) (fun _ => hJ₁ (r ≫ 𝟙 _ ≫ p₁))
  obtain ⟨I₂, hI₂, e₂⟩ := exists_good L₂ hL₂ (r z) (K := Unit) (fun _ => b ≫ p₂)
    (fun _ => J₂ (r ≫ b ≫ p₂)) (fun _ _ _ => rfl) (fun _ => hJ₂ (r ≫ b ≫ p₂))
  have h := congrArg (r.stalkMap z).hom (H (r z) I₁ I₂ hI₁ hI₂)
  rw [map_mul, map_mul, ← sval_comp p₂ s₁ r b z hI₂ (e₂ ()), ← sval_comp p₂ s₂ r b z hI₂ (e₂ ()),
    ← sval_comp p₁ s₁' r (𝟙 _) z hI₁ (e₁ ()), ← sval_comp p₁ s₂' r (𝟙 _) z hI₁ (e₁ ()), Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {T : Over S} (c : A₁ ⟶ A₂)
    [IsMonHom c] (x : T ⟶ A₁) :
    translT A₁ x ≫ T ◁ c = T ◁ c ≫ translT A₂ (x ≫ c) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {L₁ : LB A₁.left} {L₂ : LB A₂.left}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {T : Over S} (c : A₁ ⟶ A₂) [IsMonHom c] {k k' : ℤ}
    (θ : ThetaGrp A₂ L₂ k T) (θ' : ThetaGrp A₁ L₁ k' T) (hp : θ.pt = θ'.pt ≫ c)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A₂ L₂ k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A₁ L₁ k' T)}
    (h₁ : IsActOf A₂ L₂ k θ t₁ T₁) (h₂ : IsActOf A₂ L₂ k θ t₂ T₂) (h₁' : IsActOf A₁ L₁ k' θ' t₁' T₁')
    (h₂' : IsActOf A₁ L₁ k' θ' t₂' T₂') :
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) t₁ (T ◁ c).left y J₂ * sval (L := L₁) t₂' (𝟙 _) y J₁ =
        sval (L := L₂) t₂ (T ◁ c).left y J₂ * sval (L := L₁) t₁' (𝟙 _) y J₁) ↔
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) T₁ (T ◁ c).left y J₂ * sval (L := L₁) T₂' (𝟙 _) y J₁ =
        sval (L := L₂) T₂ (T ◁ c).left y J₂ * sval (L := L₁) T₁' (𝟙 _) y J₁) := by
  have cc : (T ◁ c).left ≫ (translT A₂ θ.pt).left = (translT A₁ θ'.pt).left ≫ (T ◁ c).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A₁).left) (z : Z) {J₁ J₂}, Good L₁ z J₁ → Good L₂ z J₂ →
      (sval (L := L₂) T₁ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₂' r z J₁ =
        sval (L := L₂) T₂ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₁' r z J₁ ↔
      sval (L := L₂) t₁ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₂' (r ≫ (translT A₁ θ'.pt).left) z J₁ =
        sval (L := L₂) t₂ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₁' (r ≫ (translT A₁ θ'.pt).left) z J₁) := by
    intro Z r z J₁ J₂ hJ₁ hJ₂
    rw [ThetaPowOrder.act_sval h₁ _ z hJ₂, ThetaPowOrder.act_sval h₂ _ z hJ₂, ThetaPowOrder.act_sval h₁' _ z hJ₁,
      ThetaPowOrder.act_sval h₂' _ z hJ₁, Category.assoc, cc, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L₂) t₂ _ z J₂), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (𝟙 _) y hJ₁ hJ₂).2 (cross_val hL₁ hL₂ _ _ _ t₁ t₂ t₁' t₂' H _ y hJ₁ hJ₂)
    rwa [Category.id_comp] at h
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (translT A₁ θ'.pt⁻¹).left y hJ₁ hJ₂).1 (cross_val hL₁ hL₂ _ _ _ T₁ T₂ T₁' T₂' H _ y hJ₁ hJ₂)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta₂

namespace GlobalTheory

theorem crossH_iff_of_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  intro R _ _ A₁ A₂ F _ _ c hc j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  haveI := hc
  exact CrossTheta₂.cross_act A₁.isLB A₂.isLB c θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_perm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  have h : (Finset.univ.val.map fun b => c (σ b)) = Finset.univ.val.map c := by
    conv_rhs => rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
    rfl
  funext j
  unfold symTup
  rw [h]

theorem map_symTup {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  have h : (Finset.univ.val.map fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  unfold symTup
  rw [h, map_pow]
  congr 1
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    map_multiset_prod]

theorem exists_symTup_ne_zero {K : Type} [Field K] {N : ℕ} (c : Fin N → K) (h : ∃ a, c a ≠ 0) :
    ∃ j, symTup c j ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  by_contra hne
  push Not at hne
  have hc : Multiset.card (Finset.univ.val.map c) = N := by simp
  have he : ∀ k, 0 < k → k ≤ N → (Finset.univ.val.map c).esymm k = 0 := by
    intro k hk hkN
    have := hne ⟨k - 1, by omega⟩
    unfold symTup at this
    have h2 := eq_zero_of_pow_eq_zero this
    simpa [Nat.sub_add_cancel hk] using h2
  have hp : ((Finset.univ.val.map c).map fun t => Polynomial.X - Polynomial.C t).prod = Polynomial.X ^ N := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, Finset.sum_range_succ']
    rw [Finset.sum_eq_zero]
    · simp [Multiset.esymm]
    · intro k hk
      rw [he (k + 1) (Nat.succ_pos _) (Finset.mem_range.1 hk)]
      simp
  have hev := congrArg (Polynomial.eval (c a)) hp
  rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero] at hev
  · simp only [Polynomial.eval_pow, Polynomial.eval_X] at hev
    exact pow_ne_zero N ha hev.symm
  · simp only [Multiset.mem_map]
    exact ⟨_, ⟨c a, ⟨a, Finset.mem_univ_val a, rfl⟩, rfl⟩, by simp⟩

theorem symTup_basic :
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (a : R) (j : Fin N),
      symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j) ∧
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (σ : Equiv.Perm (Fin N)),
      symTup (fun b => c (σ b)) = symTup c) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (i : R →+* R') (N : ℕ) (c : Fin N → R) (j : Fin N),
      i (symTup c j) = symTup (fun b => i (c b)) j) ∧
    ∀ (K : Type) [Field K] (N : ℕ) (c : Fin N → K), (∃ a, c a ≠ 0) → ∃ j, symTup c j ≠ 0 :=
  ⟨fun _ _ _ c a j => symTup_mul c a j, fun _ _ _ c σ => symTup_perm c σ,
    fun _ _ _ _ i _ c j => map_symTup i c j, fun _ _ _ c h => exists_symTup_ne_zero c h⟩

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveU
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_unit_of_prim : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (e : Fin N → FractionRing V), Prim (io.comp (algebraMap V (FractionRing V))) c → (∀ j, io (e j) = symTup c j) → ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro V K _ _ _ _ _ io N c e hP he
  set i := io.comp (algebraMap V (FractionRing V)) with hi
  have hio : Function.Injective io := io.injective
  have hinj : Function.Injective i := hio.comp (IsFractionRing.injective V (FractionRing V))
  letI : Algebra V K := i.toAlgebra
  have hcI : ∀ a, IsIntegral V (c a) := hP.1
  have hsI : ∀ j, IsIntegral V (symTup c j) := by
    intro j
    have : symTup c j ∈ integralClosure V K := by
      unfold symTup
      refine Subalgebra.pow_mem _ ?_ _
      rw [Finset.esymm_map_val]
      exact Subalgebra.sum_mem _ fun t _ => Subalgebra.prod_mem _ fun b _ => hcI b
    exact this
  let φ : FractionRing V →ₐ[V] K := { io with commutes' := fun r => rfl }
  have heI : ∀ j, IsIntegral V (e j) := fun j =>
    (isIntegral_algHom_iff φ hio).1 (by rw [show φ (e j) = io (e j) from rfl, he j]; exact hsI j)
  choose e' he' using fun j => IsIntegrallyClosed.isIntegral_iff.1 (heI j)
  refine ⟨e', he', ?_⟩
  obtain ⟨a₀, hc0, hinv⟩ := hP.2
  obtain ⟨W, hle⟩ := (LocalSubring.range i).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hle
  have memW : ∀ x : K, i.IsIntegralElem x → x ∈ W := by
    intro x ⟨p, hp, hx⟩
    have : IsIntegral W x := by
      let g : V →+* W := i.codRestrict W (fun v => hle ⟨v, rfl⟩)
      refine ⟨p.map g, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]; exact hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [← hy]; exact y.2
  have hcW : ∀ a, c a ∈ W := fun a => memW _ (hP.1 a)
  have hc0W : (c a₀)⁻¹ ∈ W := memW _ hinv
  let y : Fin N → W := fun a => ⟨c a * (c a₀)⁻¹, mul_mem (hcW a) hc0W⟩
  have hy0 : y a₀ = 1 := Subtype.ext (mul_inv_cancel₀ hc0)
  obtain ⟨k, hk1, hkN, hu⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) y a₀ hy0
  rw [Fintype.card_fin] at hkN
  set E := (Finset.univ.val.map y).esymm k with hE
  let u0 : W := ⟨c a₀, hcW a₀⟩
  have hu0 : IsUnit u0 := isUnit_iff_exists_inv.2 ⟨⟨(c a₀)⁻¹, hc0W⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩
  let Z : W := (u0 ^ k * E) ^ (N.factorial / k)
  have hZ : IsUnit Z := ((hu0.pow k).mul hu).pow _
  let j : Fin N := ⟨k - 1, by omega⟩
  have hjk : (j : ℕ) + 1 = k := by simp only [j]; omega
  have hZj : (Z : K) = i (e' j) := by
    have : i (e' j) = io (e j) := by rw [hi, RingHom.comp_apply, he' j]
    rw [this, he j]
    simp only [Z, symTup, hjk, hE, Finset.esymm_map_val]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.1 ht).2.symm, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [y, u0]
    field_simp
  refine ⟨j, ?_⟩
  have hmem : i (e' j) ∈ (LocalSubring.range i).toSubring := ⟨e' j, rfl⟩
  have h1 : IsUnit (Subring.inclusion hle ⟨i (e' j), hmem⟩) := by
    have h0 : Subring.inclusion hle ⟨i (e' j), hmem⟩ = Z := by apply Subtype.ext; exact hZj.symm
    rw [h0]; exact hZ
  obtain ⟨u, hu'⟩ := hloc.map_nonunit _ h1
  obtain ⟨w, hw⟩ := ((u⁻¹ : Units _) : (LocalSubring.range i).toSubring).2
  refine isUnit_iff_exists_inv.2 ⟨w, hinj ?_⟩
  have h3 : ((u : (LocalSubring.range i).toSubring) : K) * (((u⁻¹ : Units _) : (LocalSubring.range i).toSubring) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [map_mul, map_one, hw, ← h3, hu']

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialScaledFini
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

open Polynomial

private theorem symTup_mul_left {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_eq_finite (K : Type) [Field K] (N : ℕ) (e : Fin N → K) :
    {c : Fin N → K | symTup c = e}.Finite := by
  classical

  let A : Fin (N + 1) → Set K := fun k =>
    {x | ((k : ℕ) = 0 → x = 1) ∧ ∀ j : Fin N, (j : ℕ) + 1 = k → x ^ (N.factorial / ((j : ℕ) + 1)) = e j}
  have hA : ∀ k, (A k).Finite := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · exact (Set.finite_singleton (1 : K)).subset fun x hx => hx.1 hk
    · have hk1 : (k : ℕ) - 1 < N := by omega
      let j : Fin N := ⟨(k : ℕ) - 1, hk1⟩
      have hj : (j : ℕ) + 1 = k := by simp [j]; omega
      have hpos : 0 < N.factorial / ((j : ℕ) + 1) :=
        Nat.div_pos ((Nat.succ_le_of_lt j.isLt).trans (Nat.self_le_factorial N)) (Nat.succ_pos _)
      refine (Polynomial.finite_setOf_isRoot (X_pow_sub_C_ne_zero hpos (e j))).subset ?_
      intro x hx
      simp [IsRoot, hx.2 j hj]
  let V : Set (Fin (N + 1) → K) := Set.pi Set.univ A
  have hV : V.Finite := Set.Finite.pi hA
  let poly : (Fin (N + 1) → K) → K[X] := fun s =>
    ∑ k : Fin (N + 1), (-1) ^ (k : ℕ) * (C (s k) * X ^ (N - (k : ℕ)))
  let R : Set K := ⋃ p ∈ poly '' V, {x | x ∈ p.roots}
  have hR : R.Finite := (hV.image poly).biUnion fun p _ => Multiset.finite_toSet p.roots
  refine (Set.Finite.pi (t := fun _ : Fin N => R) fun _ => hR).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  let m : Multiset K := Finset.univ.val.map c
  have hm : Multiset.card m = N := by simp [m]
  let s : Fin (N + 1) → K := fun k => m.esymm k
  have hs : s ∈ V := by
    intro k _
    refine ⟨fun hk => ?_, fun j hj => ?_⟩
    · simp [s, hk, Multiset.esymm]
    · have := congrFun hc j
      simp only [symTup] at this
      simp only [s, ← hj]
      exact this
  have hpoly : poly s = (m.map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hm, Finset.sum_range (fun j => (-1) ^ j * (C (m.esymm j) * X ^ (N - j)))]
  intro a _
  simp only [R, Set.mem_iUnion, Set.mem_image]
  refine ⟨poly s, ⟨s, hs, rfl⟩, ?_⟩
  simp only [Set.mem_setOf_eq, hpoly, Polynomial.roots_multiset_prod_X_sub_C]
  exact Multiset.mem_map_of_mem c (Finset.mem_univ a)

theorem symTup_scale_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) (e : Fin N → K), ∃ T : Finset (Fin N → K),
    ∀ (c : Fin N → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) → ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T := by
  intro K _ _ N e
  refine ⟨(symTup_eq_finite K N e).toFinset, ?_⟩
  intro c a ha hc
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.factorial_pos N)
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.factorial_pos N).ne'] at hmu
    exact inv_ne_zero ha hmu.symm
  refine ⟨mu, hmu0, ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  funext j
  rw [symTup_mul_left, hmu, hc, ← _root_.mul_assoc, inv_mul_cancel₀ ha, _root_.one_mul]

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValuePointLiesOverModuliPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valPt_lies_over : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ F.X), RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ yK : X₁.S.R →+* FractionRing V₁, (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ spMap yK ≫ X₁.u = y := by
  intro g n F Z i W X₁ z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle).toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    fun a => rfl, ?_⟩
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      φ.comp ψ :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  haveI := X₁.imm
  haveI : IsProper X₁.z := X₁.isProper_compactificationMap
  haveI : Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from X₁.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {C : Type} [CommRing C] [IsLocalRing C] (q : Sp C ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint C) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro C _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of C) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap X₁.S.R.val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ X₁.u ≫ i = X₁.M.Z.fromSpecStalk w ≫ X₁.π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, X₁.comp]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono i, Category.assoc, hK]
  change spMap (φ.comp ψ) ≫ X₁.u ≫ i = y ≫ i
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightAndFlatExponentSizeBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

theorem GlobalTheory.spanShortSize : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : AllWt.Weight Dw) (n₀ : Psi H → ℤ) (hp : 1 ≤ Dw.p), laOf Dw a n = la + GlobalTheory.FlatLine.parWt Dw n₀ → (∀ τ, n₀ τ = 1 + ((n / 2 : ℕ) : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) → sizeK Dw a n ≤ (1 + ((Dw.p + Dw.q : ℕ) : ℝ)) * ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) ∧ ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
  intro E _ _ _ H Dw a n la n₀ hp hla hn₀
  have hS : ∀ τ, |(n₀ τ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1) := by
    intro τ
    have h1 : (n₀ τ : ℝ) = 1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ) := by
      rw [hn₀ τ]; simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast]
    have h2 : |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(la τ k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have h3 : (0:ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [h1]
    calc |1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ)|
        ≤ |1 + ((n / 2 : ℕ) : ℝ)| + |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (by linarith)]; linarith
  have hsum : ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
    calc ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, (∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1)) := Finset.sum_le_sum (fun τ _ => hS τ)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  refine ⟨?_, hsum⟩
  have hK : sizeK Dw a n = ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))| := by
    unfold sizeK
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hla]
    simp [GlobalTheory.FlatLine.parWt]
  have hT : sizeK Dw a n ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ τ, |(n₀ τ : ℝ)| := by
    rw [hK, Finset.mul_sum]
    calc ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))|
        ≤ ∑ τ, ∑ k : Fin (Dw.p + Dw.q), (|(la τ k : ℝ)| + |(n₀ τ : ℝ)|) :=
          Finset.sum_le_sum (fun τ _ => Finset.sum_le_sum (fun k _ => abs_add_le _ _))
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpq : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hS0 : (0:ℝ) ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hsum hpq]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickenedUniformisedGroup_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  first | exact @GlobalTheory.Mum.gtCoord_point_ext | exact GlobalTheory.Mum.gtCoord_point_ext | (intros; apply GlobalTheory.Mum.gtCoord_point_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsGaloisAllLevelsOfSquaresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_galois_all_levels_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  first | exact @GlobalTheory.Mum.galEqN_of_squares | exact GlobalTheory.Mum.galEqN_of_squares | (intros; apply GlobalTheory.Mum.galEqN_of_squares <;> assumption)
end

