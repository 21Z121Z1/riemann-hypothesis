import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.CrysConn

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def DualAbelianScheme : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧
      (∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom) ∧
      IsDual A B P ∧ IsDual B A (swap P)

def CrystallineDeRham : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X),
      Smooth s → IsSeparated s → QuasiCompact s → IsPullback i s₀ s (spMap π) →
    ∀ m : IsMor (dp0 R) s κ (s₀ ≫ spMap π) (RingHom.id R) i,
      Function.Bijective m.pull1 ∧ Function.Bijective m.pull2

def AbelianDualCrystal : Prop := DualAbelianScheme ∧ CrystallineDeRham

namespace AbelianDualCrystal

section Neron

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {A B : Over (Sp V)} [GrpObj A] [GrpObj B]

theorem hom_extends (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (f : (Over.pullback (spMap (algebraMap V K))).obj A ⟶ (Over.pullback (spMap (algebraMap V K))).obj B)
    [hf : IsMonHom f] : ∃! F : A ⟶ B, IsMonHom F ∧ (Over.pullback (spMap (algebraMap V K))).map F = f := by
  exact homExtension_semiAbelian_dvr V K A B (isSemiAbelian_of_isAbelianScheme A hA)
    (isSemiAbelian_of_isAbelianScheme B hB) f hf

end Neron

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}
  {A B A' B' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀]
  [GrpObj B₀] {i : A₀.left ⟶ A.left} {j : B₀.left ⟶ B.left} {i' : A₀.left ⟶ A'.left} {j' : B₀.left ⟶ B'.left}
  {g g' : ℕ}

theorem duality (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hB : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g' B.hom) {P : LB (A ⊗ B).left}
    (hP : IsPerfect A B P) :
    (∃! φ, IsCorrForm (dp0 R) (𝟙 _) A B P φ) ∧ ∀ φ, IsCorrForm (dp0 R) (𝟙 _) A B P φ →
      φ.IsPerfPair ∧ (∀ x, x ∈ Fil A ↔ ∀ y ∈ Fil B, φ x y = 0) ∧ ∀ y, y ∈ Fil B ↔ ∀ x ∈ Fil A, φ x y = 0 := by
  have C : CupSquare (dp0 R) (𝟙 _) (A ⊗ B) :=
    cupSquare_of_free H.1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg hg')
  obtain ⟨φ, hφ⟩ := exists_isCorrForm C hP.isLB hP.zero_left hP.zero_right
  exact ⟨⟨φ, hφ, fun φ' hφ' => IsCorrForm.unique C hP.isLB hφ' hφ⟩,
    fun φ hφ => IsCorrForm.perfect H hA hg hB hg' hP hφ⟩

theorem cupSquare_crys (H : AbelianDeRham.Free) (H' : CrystallineDeRham) (hκ : IsNilDP κ)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (h : IsPullback i A₀.hom A.hom (spMap π))
    (m : GrpMor (dp0 R) (𝟙 _) A κ (spMap π) A₀ (RingHom.id R) (spMap π) i) : CupSquare κ (spMap π) A₀ := by
  have C0 : CupSquare (dp0 R) (𝟙 _) A := cupSquare_of_free H hA hg
  have hs : Smooth (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; exact hA.smooth
  have hsep : IsSeparated (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; haveI := hA.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; haveI := hA.proper; infer_instance
  have hpb : IsPullback i A₀.hom (A.hom ≫ 𝟙 _) (spMap π) := by simpa using h
  obtain ⟨h1, h2⟩ := H' R I κ hκ R₀ π hπ hI A.left A₀.left (A.hom ≫ 𝟙 _) A₀.hom i hs hsep hqc hpb m.isMor
  exact CupSquare.of_bijective C0 m h1 h2

theorem cupSquare_crys_prod (H : AbelianDeRham.Free) (H' : CrystallineDeRham) (hκ : IsNilDP κ)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (hB : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g' B.hom)
    (h : IsGrpPullback A₀ A (spMap π) i) (k : IsGrpPullback B₀ B (spMap π) j) :
    CupSquare κ (spMap π) (A₀ ⊗ B₀) := by
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h k
  exact cupSquare_crys H H' hκ hπ hI (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB)
    (smooth_prod hg hg') (isPullback_prod h.1 k.1 l₁ l₂) (grpMor_prod (liftMor κ h) (liftMor κ k) l₁ l₂)

theorem exists_crystal_pairing (κ : DividedPowers I) (h : IsGrpPullback A₀ A (spMap π) i)
    (k : IsGrpPullback B₀ B (spMap π) j) {l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left}
    (l₁ : l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i) (l₂ : l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j)
    {P : LB (A ⊗ B).left} (hP : P.IsLB) {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : P₀.IsLB) (e : LBIso (P.pull l) P₀)
    {φ : HdR A →ₗ[R] HdR B →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) A B P φ) :
    ∃ φ₀, IsCorrForm κ (spMap π) A₀ B₀ P₀ φ₀ ∧ ∀ x y, φ₀ x y = φ (crysToDR κ h x) (crysToDR κ k y) := by
  obtain ⟨φ', h₁, h₂⟩ := IsCorrForm.pull hφ hP (liftMor κ h) (liftMor κ k) l₁ l₂ hP₀ e
  refine ⟨φ', h₁, fun x y => h₂ _ _ _ _ (fun c => ?_) (fun c => ?_)⟩
  · exact (crysToDR_apply κ h x c).symm
  · exact (crysToDR_apply κ k y c).symm

theorem polForm_unique {S : Scheme.{0}} {t : S ⟶ Sp R} {G : Over S} [GrpObj G] (C : CupSquare κ t G)
    {L : LB G.left} (hL : L.IsLB) {ψ ψ' : LinearMap.BilinForm R (Crys κ t G)} (h : IsPolForm κ t G L ψ)
    (h' : IsPolForm κ t G L ψ') : ψ = ψ' := by
  obtain ⟨n, a, b, ha, rfl⟩ := h
  obtain ⟨n', a', b', ha', rfl⟩ := h'
  have hz := ((GlobalTheory.Cris.isChern_existsUnique_and_iso R I κ G.left (G.hom ≫ t)).1 L hL).unique ha ha'
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  set E := AllPrim.dualEquiv κ t C.allPrim
  have hx : ∀ c : prim κ t G, x c = E.symm x c.1 := fun c => by
    conv_lhs => rw [← E.apply_symm_apply x]
    rfl
  have hy : ∀ c : prim κ t G, y c = E.symm y c.1 := fun c => by
    conv_lhs => rw [← E.apply_symm_apply y]
    rfl
  obtain ⟨Λ, hΛ⟩ := C.wedge (E.symm x) (E.symm y)
  have key : ∀ {m : ℕ} (a b : Fin m → prim κ t G),
      wedgeForm κ t G a b x y = Λ (∑ k, cup _ (a k).1 (b k).1) := by
    intro m a b
    rw [wedgeForm_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hΛ, hx (a k), hx (b k), hy (a k), hy (b k)]
  rw [key, key, hz]

variable {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  {T : Type} [CommRing T] [Algebra T R] [Module T M] [IsScalarTower T R M]

end AbelianDualCrystal

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Elliptic

abbrev toInt : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv

theorem exists_int (c : (1 : FracId ℚ).elt) : ∃ n : ℤ, (n : ℚ) = c := by
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 ℚ)⁰).1 c.2
  exact ⟨toInt a, by rw [Rat.ringOfIntegersEquiv_apply_coe]; exact ha⟩

def eltInt (c : (1 : FracId ℚ).elt) : ℤ := (exists_int c).choose

theorem eltInt_spec (c : (1 : FracId ℚ).elt) : (eltInt c : ℚ) = c := (exists_int c).choose_spec

theorem eltInt_add (c c' : (1 : FracId ℚ).elt) : eltInt (c + c') = eltInt c + eltInt c' := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_add, eltInt_spec, eltInt_spec, eltInt_spec, Submodule.coe_add]

theorem eltInt_smul (a : 𝓞 ℚ) (c : (1 : FracId ℚ).elt) : eltInt (a • c) = toInt a * eltInt c := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, eltInt_spec, eltInt_spec, Submodule.coe_smul, Algebra.smul_def,
    Rat.ringOfIntegersEquiv_apply_coe]

def oneElt : (1 : FracId ℚ).elt := ⟨1, (FractionalIdeal.mem_one_iff (𝓞 ℚ)⁰).2 ⟨1, map_one _⟩⟩

theorem eltInt_one : eltInt oneElt = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [eltInt_spec, Int.cast_one]
  rfl

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def ratAct : OAct (𝓞 ℚ) A where
  act a := (Serre.intAct A).act (toInt a)
  hom a := (Serre.intAct A).hom _
  one := by rw [map_one]; exact (Serre.intAct A).one
  mul a b := by rw [map_mul]; exact (Serre.intAct A).mul _ _
  add a b := by rw [map_add]; exact (Serre.intAct A).add _ _

variable {A}

theorem comp_ratAct {T : Over S} (x : T ⟶ A) (a : 𝓞 ℚ) : x ≫ (ratAct A).act a = x ^ toInt a := by
  show x ≫ (Serre.intAct A).act (toInt a) = _
  unfold Serre.intAct
  rw [GrpObj.comp_zpow, Category.comp_id]

theorem lam_zpow_left {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) {T : Over S}
    (x y : T ⟶ A) (n : ℤ) : lam (cls L hL) (x ^ n) y = n • lam (cls L hL) x y := by
  have key : ∀ m : ℕ, lam (cls L hL) (x ^ (m : ℤ)) y = (m : ℤ) • lam (cls L hL) x y := fun m ↦ by
    rw [zpow_natCast, lam_pow_left hL hΘ, natCast_zsmul]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact key m
  · have h := lam_mul_left hL hΘ (x ^ (-(m : ℤ))) (x ^ (m : ℤ)) y
    rw [← zpow_add, neg_add_cancel, zpow_zero, lam_one_left, key] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero, ← h]

theorem lam_zpow_right {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) {T : Over S}
    (x y : T ⟶ A) (n : ℤ) : lam (cls L hL) x (y ^ n) = n • lam (cls L hL) x y := by
  rw [lam_comm, lam_zpow_left hL hΘ, lam_comm]

def mulLam (L : LB A.left) (n : ℤ) : LB (G2 A).left := cubeLB A ![fst A A, snd A A ^ n] L

theorem isLB_mulLam {L : LB A.left} (hL : L.IsLB) (n : ℤ) : (mulLam L n).IsLB := LB.isLB_linComb hL _ _

theorem cls_mulLam {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) (n : ℤ) :
    cls _ (isLB_mulLam hL n) = n • lam (cls L hL) (fst A A) (snd A A) :=
  (cls_cube_two hL (fst A A) (snd A A ^ n) (isLB_mulLam hL n)).trans (lam_zpow_right hL hΘ _ _ n)

theorem cls_pull_mulLam {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) (n : ℤ)
    {T : Over S} (x y : T ⟶ A) :
    cls _ (pull_isLB (isLB_mulLam hL n) (lift x y).left) = n • lam (cls L hL) x y := by
  rw [cls_pull (isLB_mulLam hL n), cls_mulLam hL hΘ, map_zsmul, pull_lam, lift_fst, lift_snd]

theorem cls_pull_lam {L : LB A.left} (hL : L.IsLB) {T : Over S} (x y : T ⟶ A)
    (h : ((abelian₂ A L).pull (lift x y).left).IsLB) : cls _ h = lam (cls L hL) x y := by
  rw [cls_pull (L := abelian₂ A L) (LB.isLB_linComb hL _ _) _ h]
  erw [cls_cube_two hL (fst A A) (snd A A)]
  rw [pull_lam, lift_fst, lift_snd]

end

variable {k : Type} [Field k] [IsAlgClosed k] (Q : Out.PolAV (Sp k)) (hg : Q.g = 1)

def obj : Obj ℚ 1 (Sp k) :=
  haveI := Q.isAb.comm
  haveI := Q.isAb.proper
  have hΘ := exists_gen_theta_of_isAbelianScheme k Q.A Q.isAb Q.L Q.isLB
  have hL := Q.isLB
  { A := Q.A
    ab := Q.isAb
    dim := by rw [Module.finrank_self, ← hg]; exact Q.smoothDim
    rm := ratAct Q.A
    P c := mulLam Q.L (eltInt c)
    isLB c := isLB_mulLam hL _
    rig₁ c := (cls_eq_zero_iff (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, lam_one_left, smul_zero])
    rig₂ c := (cls_eq_zero_iff (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, lam_one_right, smul_zero])
    symm c := (cls_eq_iff (isLB_mulLam hL _) (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, cls_mulLam hL hΘ, lam_comm])
    add c c' := (cls_eq_iff (isLB_mulLam hL _) (LB.isLB_div (isLB_mulLam hL _) (isLB_mulLam hL _))).1 (by
      rw [cls_div (isLB_mulLam hL _) (isLB_mulLam hL _), cls_mulLam hL hΘ, cls_mulLam hL hΘ, cls_mulLam hL hΘ,
        eltInt_add, add_smul, add_sub_cancel_left])
    smul a c := (cls_eq_iff (isLB_mulLam hL _) (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, cls_mulLam hL hΘ, comp_ratAct, lam_zpow_right hL hΘ, eltInt_smul, smul_smul,
        mul_comm])
    pos c hc := by
      have h0 : 0 < eltInt c := by
        have := hc (Rat.castHom ℝ)
        rw [← eltInt_spec] at this
        simpa using this
      have hD := pull_isLB (L := abelian₂ Q.A Q.L) (LB.isLB_linComb hL _ _) (lift (𝟙 Q.A) (𝟙 Q.A)).left
      refine (GlobalTheory.KeyAtFam.relAmple_iff_of_cls hD (pull_isLB (isLB_mulLam hL _) _) (d := (eltInt c).toNat) (by omega) ?_).2
        (EighthPowerFactor.relAmple_diag_lam Q.isAb hL hΘ Q.ample)
      rw [cls_pull_mulLam hL hΘ, cls_pull_lam hL, ← natCast_zsmul, Int.toNat_of_nonneg h0.le]
    ker c T x hx a ha := by
      have h₁ := (cls_eq_zero_iff (pull_isLB (isLB_mulLam hL _) _)).2 hx
      rw [cls_pull_mulLam hL hΘ, ← lam_zpow_right hL hΘ, lam_comm, ← GrpObj.comp_zpow] at h₁
      have h₂ : x ^ eltInt c = 1 := SiegelOfPolarised.eq_one_of_lam hL Q.ktriv _
        ((cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ((cls_pull_lam hL _ _ _).trans h₁))
      obtain ⟨b, hb⟩ := ha oneElt
      have h₃ := congrArg eltInt hb
      rw [eltInt_smul, eltInt_smul, eltInt_one, _root_.mul_one] at h₃
      rw [comp_ratAct, h₃, mul_comm, zpow_mul, h₂, one_zpow] }

end GlobalTheory.RealMult.Elliptic

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]

def Obj.DetGen.ofBasis (X : Obj F 𝔠 (Sp R)) (b : Module.Basis (Fin (Module.finrank ℚ F)) R X.Lie) : X.DetGen :=
  ⟨b.det, eq_top_iff.2 fun f _ ↦ Submodule.mem_span_singleton.2 ⟨f b, (AlternatingMap.eq_smul_basis_det b f).symm⟩⟩

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def PoincareDeRhamDuality : Prop :=
  ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A →
    IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, GlobalTheory.AbDual.IsDual A B P →
    ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
      LinearMap.IsPerfPair φ ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0

end GlobalTheory.Published
end
end

