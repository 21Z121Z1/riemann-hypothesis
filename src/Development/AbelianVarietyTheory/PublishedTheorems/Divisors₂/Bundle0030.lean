import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def ConjugateFiltration : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (hA : (p : Γ(A.left, ⊤)) = 0) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)
        (spMap (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)) (GlobalTheory.VB.frob A.left p hA)),
      (∀ x ∈ PrimitiveSubmodule A, m.pull x = 0) ∧
      (∃ N : Submodule R (primDR A), IsCompl (Submodule.span R (Set.range m.pull)) N) ∧
      (∀ P : PrimeSpectrum R, Module.rankAtStalk (Submodule.span R (Set.range m.pull)) P = g) ∧
      ∀ (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      ∀ (hB : (p : Γ(B.left, ⊤)) = 0) (n : GrpMor (dp0 R) (𝟙 _) B (dp0 R) (𝟙 _) B (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)
          (spMap (GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR)) (GlobalTheory.VB.frob B.left p hB)) (P : LB (A ⊗ B).left),
        GlobalTheory.AbDual.IsDual A B P →
      ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
        ∀ (x : HdR A) (y : HdR B), (∀ c, x (m.pull c) = 0) → (∀ c, y (n.pull c) = 0) → φ x y = 0

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent unitOn)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta)
open ReciprocityTheory.ChartRestriction.G.Out (WeilIs)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R)

def IsConnecting (x : G.VecExt) (b : G.A 1) : Prop :=
  ∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
    G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b

variable {G}

theorem IsConnecting.sub {x x' : G.VecExt} {b b' : G.A 1} (h : G.IsConnecting x b)
    (h' : G.IsConnecting x' b') : G.IsConnecting (x - x') (b - b') := by
  obtain ⟨c, B, rfl, h₁, h₂, rfl⟩ := h
  obtain ⟨c', B', rfl, h₁', h₂', rfl⟩ := h'
  exact ⟨c - c', B - B', rfl, by rw [map_sub, map_sub, h₁, h₁'], by rw [map_sub, h₂, h₂', sub_zero], rfl⟩

theorem IsConnecting.unique (hp : (p : R) = 0) {x : G.VecExt} {b b' : G.A 1}
    (h : G.IsConnecting x b) (h' : G.IsConnecting x b') : b = b' := by
  obtain ⟨c, B, h₀, h₁, h₂, h₃⟩ := h.sub h'
  rw [sub_self, Submodule.Quotient.mk_eq_zero] at h₀
  obtain ⟨D, rfl⟩ := h₀
  rw [cocyclesMap_cob, ← sub_eq_zero, ← map_sub] at h₁
  set E := B - funsMap ((p : ℤ_[p]) • 𝟙 G) D with hE
  have e₂ : cobOne R _ (E.1 2) = 0 := congrArg (fun z : G.cocycles ↦ z.1 2) h₁
  have e₃ : G.mulP 1 (E.1 1) = 0 := by
    rw [← E.2 1, mulP_res, (mulBy_of_cobOne_eq_zero e₂ p).1, ← Nat.cast_smul_eq_nsmul R, hp, zero_smul]
  have e₁ : E.1 1 = 0 := CartierDual.eq_of_forall_apply (R := R) fun φ ↦ by
    obtain ⟨ψ, rfl⟩ := G.dual_mulP_surjective 1 φ
    exact (congrArg ψ.ofConv e₃).trans ((map_zero _).trans (map_zero _).symm)
  have e₄ : b - b' = algebraMap R _ (Coalgebra.counit (D.1 1)) := by
    rw [← h₃, ← G.mulBy_pow_self, pow_one, ← natCast_smul_id_app]
    exact sub_eq_zero.1 e₁
  rw [e₄, Bialgebra.counit_algebraMap] at h₂
  rw [← sub_eq_zero, e₄, h₂, map_zero]

end PDivGroup

namespace EpsWeil

variable {R : Type} [CommRing R] (D : Type) [CommRing D] [Algebra R D]

variable {D} in

def epsUnit (b : D) : (DualNumber D)ˣ where
  val := 1 + TrivSqZeroExt.inr b
  inv := 1 - TrivSqZeroExt.inr b
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

variable (R) in

def epsMap : DualNumber R →ₐ[R] DualNumber D :=
  DualNumber.lift ⟨(Algebra.ofId R _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩

variable {D} {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def PairsTo (P : LB (A ⊗ B).left) (n : ℕ) (x : PDiv.SpAlg R D ⟶ A) (v : epsR R ⟶ B) (b : D) : Prop :=
  WeilIs (A ⊗ B) P (n : ℤ) (T := PDiv.SpAlg R (DualNumber D))
    (lift (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x) 1) (lift 1 (spOver (epsMap R D) ≫ v))
    (unitOn (epsUnit b))

theorem unitOn_bijective : Function.Bijective (unitOn (R := D)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of D)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem map_unitOn {D' : Type} [CommRing D'] (f : D →+* D') (u : Dˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) :=
  Units.ext (congrArg (fun q ↦ q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

end EpsWeil

namespace Published

namespace BarsottiTateDieudonne

def WittModule : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : PDivGroup p k → ModuleCat.{0} (WittVector p k))
      (map : ∀ G H : PDivGroup p k, (G ⟶ H) →+ (M H →ₗ[WittVector p k] M G))
      (red : ∀ G : PDivGroup p k,
        M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt),
      (∀ G : PDivGroup p k, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
        Module.finrank (WittVector p k) (M G) = G.height ∧ Function.Surjective (red G) ∧
        (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧ map G G (𝟙 G) = LinearMap.id) ∧
      (∀ (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K),
        map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
      ∀ (G H : PDivGroup p k) (f : G ⟶ H) (m : M H),
        red G (map G H f m) = PDivGroup.rigExtMap f (red H m)

def WeilCompatible {p : ℕ} [Fact p.Prime] (e : DeRhamVectorExtension.Family p) (s : ℤˣ) : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : (p : R) = 0) ⦃A B : Over (Sp R)⦄ [GrpObj A] [GrpObj B] ⦃g : ℕ⦄
    (hA : IsAbelianScheme A), IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g B.hom → ∀ ⦃P : LB (A ⊗ B).left⦄, AbDual.IsDual A B P →
    ∀ ⦃φ : HdR A →ₗ[R] HdR B →ₗ[R] R⦄, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) ⦃h' : HdR B⦄ ⦃v : epsR R ⟶ B⦄, IsLieImage h' v →
    ∀ ⦃b : G.A 1⦄, EpsWeil.PairsTo P p (t.y 1) v b →
    ∀ ⦃c : primDR A⦄, (∀ h ∈ Fil A, φ h h' = h c) →
      G.IsConnecting (G.rigToExt (e (hR ▸ IsNilpotent.zero) hA t c)) (s • b)

def HodgeQuotient : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ (e : DeRhamVectorExtension.Family p) (s : ℤˣ),
    e.Natural ∧ e.Filtered ∧ e.Tangent ∧ WeilCompatible e s

end BarsottiTateDieudonne

def BarsottiTateDieudonne : Prop :=
  BarsottiTateDieudonne.WittModule ∧ BarsottiTateDieudonne.HodgeQuotient

namespace BarsottiTateDieudonne

theorem HodgeQuotient.deRhamVectorExtension (H : HodgeQuotient) : DeRhamVectorExtension := fun p _ ↦
  have ⟨e, _, h₁, h₂, h₃, _⟩ := H p
  ⟨e, h₁, h₂, h₃⟩

theorem deRhamVectorExtension (H : BarsottiTateDieudonne) : DeRhamVectorExtension :=
  H.2.deRhamVectorExtension

end BarsottiTateDieudonne

end Published

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.H2EqZeroOfIsInitial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDualCrystal.Test

section Dual

variable {S : Scheme.{0}} {A B A₁ B₁ : Over S} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
  {P : LB (A ⊗ B).left} {P₁ : LB (A₁ ⊗ B₁).left}

theorem point_ext (h : IsDual A B P) {T : Over S} {x y : T ⟶ B}
    (e : evc h.isLB (fst A T) (snd A T ≫ x) = evc h.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB h.isLB _
  refine (h.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.additive _ _ _ _

theorem exists_dualHom (h : IsDual A B P) (h' : IsDual B A (swap P)) (h₁ : IsDual A₁ B₁ P₁)
    (h₁' : IsDual B₁ A₁ (swap P₁)) (u : A ⟶ A₁) [IsMonHom u] :
    ∃ v : B₁ ⟶ B, IsMonHom v ∧ LBIso (ev P (fst A B₁) (snd A B₁ ≫ v)) (ev P₁ (fst A B₁ ≫ u) (snd A B₁)) ∧
      ∀ v' : B₁ ⟶ B, LBIso (ev P (fst A B₁) (snd A B₁ ≫ v')) (ev P₁ (fst A B₁ ≫ u) (snd A B₁)) → v' = v := by
  have hM : (ev P₁ (fst A B₁ ≫ u) (snd A B₁)).IsLB := pull_isLB h₁.isLB _
  obtain ⟨v, hv, hu⟩ := h.univ B₁ _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    simp only [evc_ev h₁.isLB, lift_fst_assoc, lift_snd, MonObj.mul_comp]
    exact (isAdditive_iff h₁.isLB).1 h₁.additive _ _ _ _)
  have e := (cls_eq_iff hM (pull_isLB h.isLB _)).2 hv
  have k : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B₁), evc h.isLB a (b ≫ v) = evc h₁.isLB (a ≫ u) b := fun Y a b ↦ by
    have := congrArg (CechPic.pull (lift a b).left) e
    rw [cls_ev h₁.isLB, cls_ev h.isLB, pull_evc, pull_evc] at this
    simpa using this.symm
  have add : ∀ {C D : Over S} [GrpObj C] [GrpObj D] {Q : LB (C ⊗ D).left} (hQ : Q.IsLB) (_ : IsDual D C (swap Q))
      (Y : Over S) (a : Y ⟶ C) (b b' : Y ⟶ D), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro C D _ _ Q hQ q Y a b b'
    simpa only [evc_swap hQ] using (isAdditive_iff q.isLB).1 q.additive Y b b' a
  have m : ∀ (Y : Over S) (b b' : Y ⟶ B₁), (b * b') ≫ v = (b ≫ v) * (b' ≫ v) := fun Y b b' ↦
    point_ext h (by
      rw [← Category.assoc, k, MonObj.comp_mul, MonObj.comp_mul, add h₁.isLB h₁', add h.isLB h',
        ← Category.assoc, ← Category.assoc, k, k])
  refine ⟨v, ⟨?_, ?_⟩, (cls_eq_iff (pull_isLB h.isLB _) hM).1 e.symm,
    fun v' hv' ↦ hu v' ((cls_eq_iff hM (pull_isLB h.isLB _)).1 ((cls_eq_iff (pull_isLB h.isLB _) hM).2 hv').symm)⟩
  · have := m (𝟙_ _) 1 1
    rw [_root_.mul_one] at this
    have e1 : (1 : 𝟙_ (Over S) ⟶ B₁) ≫ v = 1 := left_eq_mul.1 this
    simpa [Hom.one_def] using e1
  · have := m (B₁ ⊗ B₁) (fst _ _) (snd _ _)
    simpa [Hom.mul_def, lift_fst_comp_snd_comp] using this

theorem dual_unique {B' : Over S} [GrpObj B'] {P' : LB (A ⊗ B').left} (h : IsDual A B P) (h' : IsDual A B' P') :
    Nonempty (B ≅ B') := by
  have key : ∀ {C D : Over S} [GrpObj C] [GrpObj D] {Q : LB (A ⊗ C).left} {Q' : LB (A ⊗ D).left}
      (q : IsDual A C Q) (q' : IsDual A D Q'), ∃ x : C ⟶ D, ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ C),
        evc q'.isLB a (b ≫ x) = evc q.isLB a b := by
    intro C D _ _ Q Q' q q'
    obtain ⟨x, hx, -⟩ := q'.univ C Q q.isLB q.additive
    refine ⟨x, fun Y a b ↦ ?_⟩
    have := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff q.isLB (pull_isLB q'.isLB _)).2 hx)
    rw [cls_ev q'.isLB, pull_evc] at this
    simpa [evc] using this.symm
  obtain ⟨x, hx⟩ := key h h'
  obtain ⟨y, hy⟩ := key h' h
  exact ⟨⟨x, y, point_ext h (by rw [← Category.assoc, hy, hx, Category.comp_id]),
    point_ext h' (by rw [← Category.assoc, hx, hy, Category.comp_id])⟩⟩

theorem id_eq_one_of_dual (h : IsDual A B P) (h' : IsDual B A (swap P)) (e : 𝟙 B = 1) : 𝟙 A = 1 := by
  have p := h.isPerfect h'
  refine p.ker_left _ _ ((triv_ev_iff h.isLB _ _).2 ?_)
  rw [← Category.comp_id (snd A B), e, MonObj.comp_one, evc_one_right h.isLB h.zero]

theorem id_eq_one_of_triv (h : IsDual A B (LB.triv _)) : 𝟙 B = 1 :=
  h.eq_one _ ((triv_ev_iff h.isLB _ _).2 (map_zero _))

theorem isDual_unit_swap : IsDual (𝟙_ (Over S)) (𝟙_ (Over S)) (swap (LB.triv _)) := by
  have hs : (swap (LB.triv (𝟙_ (Over S) ⊗ 𝟙_ (Over S)).left)).IsLB := pull_isLB (LB.isLB_triv _) _
  have h0 : ∀ (Y : Over S) (a b : Y ⟶ 𝟙_ (Over S)), evc hs a b = 0 := fun _ _ _ ↦ by
    rw [evc_swap (LB.isLB_triv _)]; exact map_zero _
  refine ⟨hs, (isAdditive_iff hs).2 fun _ _ _ _ ↦ by simp only [h0, add_zero],
    (triv_ev_iff hs _ _).2 (h0 _ _ _), fun T M hM ha ↦ ⟨toUnit T, ?_, fun _ _ ↦ toUnit_unique _ _⟩⟩
  refine (cls_eq_iff hM (pull_isLB hs _)).1 ?_
  have e := ha.evc_one hM (snd (𝟙_ (Over S)) T)
  rw [toUnit_unique 1 (fst _ T), evc, lift_fst_snd, Over.id_left, CechPic.pull_id] at e
  rw [e, cls_ev hs, h0]

theorem elliptic_dual (H : DualAbelianScheme) {R : Type} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (P : LB ((WeierstrassCurve.ellPolAV W).A ⊗ B).left), IsAbelianScheme B ∧
      SmoothOfRelativeDimension 1 B.hom ∧ IsPerfect _ B P := by
  obtain ⟨B, _, P, hB, hg, h, h'⟩ := H _ _ (WeierstrassCurve.ellPolAV W).isAb
  exact ⟨B, _, P, hB, hg 1 (WeierstrassCurve.ellPolAV W).smoothDim, h.isPerfect h'⟩

end Dual

section Crystal

theorem h2_eq_zero_of_isInitial {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T₀ : C}
    (h : Limits.IsInitial T₀) (c : CatCoh.H2 F) : c = 0 := by
  obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective F c
  refine CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩
  funext T T' T'' φ ψ
  have := z.2 (h.to T) φ ψ
  rw [h.to_comp] at this
  rw [d1_apply]
  linear_combination this

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}

def baseThick (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Thick κ (spMap π) where
  B := R
  J := I
  δ := κ
  nil := hκ
  dp := (DPMorphism.id κ).isDPMorphism
  B₀ := R₀
  π := π
  surj := hπ
  ker b := by rw [← hI]; rfl
  x := 𝟙 _
  w := Category.id_comp _

theorem nonempty_isInitial (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) :
    Nonempty (Limits.IsInitial (baseThick hκ hπ hI)) := by
  have ex : ∀ T : Thick κ (spMap π), Nonempty (baseThick hκ hπ hI ⟶ T) := fun T ↦ by
    obtain ⟨f, hf⟩ := Spec.map_surjective T.x
    have w := T.w
    rw [← hf, ← Spec.map_comp] at w
    have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
    exact ⟨⟨Algebra.ofId R T.B, f.hom, fun b ↦ RingHom.congr_fun w' b, T.dp, (Category.comp_id _).trans hf⟩⟩
  exact ⟨Limits.IsInitial.ofUniqueHom (fun T ↦ (ex T).some) fun T m ↦ Thick.hom_ext fun b ↦
    (m.φ.commutes b).trans ((ex T).some.φ.commutes b).symm⟩

theorem base_case (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    (m : IsMor (dp0 R) (spMap (RingHom.id R)) κ (spMap π) (RingHom.id R) (spMap π)) :
    Function.Bijective m.pull1 ∧ Function.Bijective m.pull2 := by
  obtain ⟨a⟩ := nonempty_isInitial hκ hπ hI
  obtain ⟨b⟩ := nonempty_isInitial (isDPNilpotent_bot R) (π := RingHom.id R) Function.surjective_id
    ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)
  exact ⟨⟨fun x y _ ↦ (H1.eq_zero_of_isInitial _ b x).trans (H1.eq_zero_of_isInitial _ b y).symm,
      fun y ↦ ⟨0, (map_zero _).trans (H1.eq_zero_of_isInitial _ a y).symm⟩⟩,
    ⟨fun x y _ ↦ (h2_eq_zero_of_isInitial _ b x).trans (h2_eq_zero_of_isInitial _ b y).symm,
      fun y ↦ ⟨0, (map_zero _).trans (h2_eq_zero_of_isInitial _ a y).symm⟩⟩⟩

theorem trivial_case {X : Scheme.{0}} (s : X ⟶ Sp R) (m : IsMor (dp0 R) s (dp0 R) s (RingHom.id R) (𝟙 X)) :
    Function.Bijective m.pull1 ∧ Function.Bijective m.pull2 :=
  ⟨by rw [show (m.pull1 : _ → _) = id from funext m.pullCohomologyOne_id]; exact Function.bijective_id,
    by rw [show (m.pull2 : _ → _) = id from funext m.pullCohomologyTwo_id]; exact Function.bijective_id⟩

theorem elliptic_crystal (H : CrystallineDeRham) (R : Type) [CommRing R] (W : WeierstrassCurve (DualNumber R))
    [W.IsElliptic] : ∃ (i : _) (m : IsMor (dp0 _) (WeierstrassCurve.ellPolAV W).A.hom (epsDP R)
      ((WeierstrassCurve.ellPolAV (W.map (TrivSqZeroExt.fstHom R R R).toRingHom)).A.hom ≫
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (RingHom.id _) i),
      Function.Bijective m.pull1 ∧ Function.Bijective m.pull2 := by
  have h := GlobalTheory.WeierstrassCurve.isGrpPullback_ellPolAV W (TrivSqZeroExt.fstHom R R R).toRingHom rfl
  have := (WeierstrassCurve.ellPolAV W).isAb.smooth
  have := (WeierstrassCurve.ellPolAV W).isAb.proper
  exact ⟨_, IsMor.of_dividedPowersZeroIdeal _ (by rw [Cris.spMap_id, Category.comp_id]; exact h.1.w),
    H _ _ _ (isDPNilpotent_squareZero _) R _ (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl _ _ _ _ _ inferInstance inferInstance
      inferInstance h.1 _⟩

end Crystal

end GlobalTheory.Published.AbelianDualCrystal.Test
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def IsFineModuli {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) {N : ℕ} {U : Obj F 𝔠 M}
    (α : U.Level N) : Prop :=
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp B) (X : Obj F 𝔠 S) (β : X.Level N),
    ∃! b : S ⟶ M, b ≫ s = t ∧ Obj.IsLevelPull β α b

def IsRelCI {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) (n : ℕ) : Prop :=
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp B), topologicalKrullDim ↥(pullback s t) = n) ∧
    ∀ x : M, ∃ (V : M.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (c : ℕ) (g : Fin c → MvPolynomial (Fin (c + n)) B)
      (e : Γ(M, V) ≃+* MvPolynomial (Fin (c + n)) B ⧸ Ideal.span (Set.range g)),
      ∀ b : B, e (constFn s V b) = Ideal.Quotient.mk _ (MvPolynomial.C b)

def Obj.IsLinearKS {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ (a : 𝓞 F) (x y : Fil X.A), (y : HdR X.A) = act (dp0 R) (𝟙 _) X.rm a x → κ y = a • κ x

def Obj.HasKS {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp (DualNumber R))}
    {i : X.A.left ⟶ X'.A.left} (h : X.IsPullBy X' (DeRham.epsRed R) i) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ x : Fil X.A, IsKSValue h.grp (x : HdR X.A) (κ x).hom

def TorusPointsExist : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (𝔞 𝔟 : FracId F), ∀ z ∈ halfSpace F,
    ∃ (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetGen), X.IsRapoport ∧ IsTorusPoint e 𝔞 𝔟 z X δ.1

def QExpansionOnAll : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) (k : ℕ) (R₀ : Subring ℂ)
      (g : ((F →+* ℝ) → ℂ) → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      IsHolForm 𝔞 𝔟 k g → HasFourier 𝔞 𝔟 g a → (∀ ξ, a ξ ∈ R₀) →
      ∃! r : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) R₀ k, r.HasValues e 𝔞 𝔟 g

end GlobalTheory.RealMult

namespace GlobalTheory.Published

def DelignePappasModel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 3 ≤ N →
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N),
      IsFineModuli s α ∧ IsSeparated s ∧ QuasiCompact s ∧ LocallyOfFinitePresentation s ∧
      Flat s ∧ IsRelCI s (Module.finrank ℚ F) ∧
      (∃ V : M.Opens, (V : Set M) = U.rapLocus ∧ SmoothOfRelativeDimension (Module.finrank ℚ F) (V.ι ≫ s) ∧
        M.basicOpen ((discr F : ℤ) : Γ(M, ⊤)) ≤ V ∧
        ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
          pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) ∧
      (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) ∧
      ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra (Localization.Away (N : ℤ)) B]
        [IsCyclotomicExtension {N} (Localization.Away (N : ℤ)) B]
        (x : ↥(pullback s (spMap (algebraMap (Localization.Away (N : ℤ)) B))))
        (K : Type) [Field K] (t : Sp K ⟶ Sp B),
        IsIrreducible (pullback.fst (pullback.snd s (spMap (algebraMap (Localization.Away (N : ℤ)) B))) t ⁻¹'
          connectedComponent x)

def HilbertQExpansion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) (k : ℕ) (R₀ : Subring ℂ)
      (g : ((F →+* ℝ) → ℂ) → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      IsHolForm 𝔞 𝔟 k g → HasFourier 𝔞 𝔟 g a → (∀ ξ, a ξ ∈ R₀) →
      ∃! r : Rule (rapObj (𝔞 * 𝔟⁻¹)) R₀ k, r.HasValues e 𝔞 𝔟 g

def GoetzkyKoecher : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (𝔞 𝔟 : FracId F) (k : ℕ) (g : ((F →+* ℝ) → ℂ) → ℂ), IsHolForm 𝔞 𝔟 k g →
      (∃! a, HasFourier 𝔞 𝔟 g a) ∧
      ∀ a, HasFourier 𝔞 𝔟 g a → ∀ ξ, a ξ ≠ 0 → ξ = 0 ∨ IsTotPos (ξ : F)

def HilbertKodairaSpencer : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)), X.IsRapoport →
    (∀ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left) (h : X.IsPullBy X' (DeRham.epsRed R) i),
      ∃! κ, X.IsLinearKS κ ∧ Obj.HasKS h κ) ∧
    (∀ κ, X.IsLinearKS κ → ∃ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left)
      (h : X.IsPullBy X' (DeRham.epsRed R) i), Obj.HasKS h κ) ∧
    ∀ (X' X'' : Obj F 𝔠 (Sp (DualNumber R))) (i' : X.A.left ⟶ X'.A.left) (i'' : X.A.left ⟶ X''.A.left)
      (h' : X.IsPullBy X' (DeRham.epsRed R) i') (h'' : X.IsPullBy X'' (DeRham.epsRed R) i'') κ, Obj.HasKS h' κ → Obj.HasKS h'' κ →
      ∃ ψ : X'.A.left ⟶ X''.A.left, X'.IsPullBy X'' (𝟙 _) ψ ∧ i' ≫ ψ = i''

def RealMultDeRhamRank : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsLocalRing R]
    (X : Obj F 𝔠 (Sp R)),
    letI := tensorModule (dp0 R) (𝟙 _) X.rm
    Nonempty (Module.Basis (Fin 2) (R ⊗[ℤ] 𝓞 F) (HdR X.A))

def HilbertBlumenthal : Prop :=
  DelignePappasModel ∧ HilbertQExpansion ∧ GoetzkyKoecher ∧ HilbertKodairaSpencer ∧ RealMultDeRhamRank

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Published

def SiegelToroidalPolCharts : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (_ : IsOpenImmersion j)
      (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
      IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
      (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
      IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
      1 ≤ d ∧ (∀ x : S, GlobalTheory.PolDeg.HasPolChart F s j e φ BD d x) ∧
      1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
      ∃ k : ℕ, IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

end GlobalTheory.Published
end
end

