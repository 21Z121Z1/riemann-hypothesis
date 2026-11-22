import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3353
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

section

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem pow_smul_cancel {G H : PDivGroup p k} (a : ℕ) {X Y : G ⟶ H}
    (h : (p : ℤ_[p]) ^ a • X = (p : ℤ_[p]) ^ a • Y) : X = Y := by
  induction a generalizing X Y with
  | zero => simpa using h
  | succ a ih =>
    apply ih
    rw [← sub_eq_zero, ← smul_sub]
    apply eq_zero_of_prime_smul_eq_zero
    rw [smul_smul, ← pow_succ', smul_sub, h, sub_self]

theorem finrank_A (G : PDivGroup p k) (n : ℕ) : Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  simpa [Module.rankAtStalk_eq_finrank_of_free] using h

theorem isIsog_pow_smul_id (G : PDivGroup p k) (m : ℕ) : IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) :=
  ⟨m, 𝟙 G, Category.comp_id _, Category.id_comp _⟩

theorem hasLogDeg_pow_smul_id (G : PDivGroup p k) (m : ℕ) :
    HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height) := by
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨f, hf, hk⟩ := G.exists_res_le hn
  have e : Hom.app ((p : ℤ_[p]) ^ m • 𝟙 G) n = mulBy k _ (p ^ m) := by
    rw [← Nat.cast_pow, natCast_smul_id_app]
  rw [e]
  change Module.finrank k (G.A n ⧸ torsionIdeal k (G.A n) (p ^ m)) = _
  rw [← hk]
  exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq).trans
    (finrank_A G m)

theorem isIsog_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hg : IsIsog g) : IsIsog (f ≫ g) := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, g', h3, h4⟩ := hg
  refine ⟨a + b, g' ≫ f', ?_, ?_⟩
  · calc (f ≫ g) ≫ g' ≫ f' = f ≫ (g ≫ g') ≫ f' := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 G := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h1, smul_smul, ← pow_add,
          add_comm b a]
  · calc (g' ≫ f') ≫ f ≫ g = g' ≫ (f' ≫ f) ≫ g := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by
        rw [h2, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h4, smul_smul, ← pow_add]

theorem isIsog_of_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hfg : IsIsog (f ≫ g)) : IsIsog g := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, u, h3, h4⟩ := hfg
  refine ⟨a + b, (p : ℤ_[p]) ^ a • (u ≫ f), ?_, ?_⟩
  · calc g ≫ ((p : ℤ_[p]) ^ a • (u ≫ f)) = ((p : ℤ_[p]) ^ a • 𝟙 H) ≫ g ≫ u ≫ f := by
          rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
      _ = f' ≫ ((f ≫ g) ≫ u) ≫ f := by rw [← h2]; simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 H := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h2, smul_smul, ← pow_add,
          add_comm b a]
  · calc ((p : ℤ_[p]) ^ a • (u ≫ f)) ≫ g = (p : ℤ_[p]) ^ a • (u ≫ f ≫ g) := by
          rw [Linear.smul_comp, Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by rw [h4, smul_smul, ← pow_add]

variable [CharP k p]

theorem hasLogDeg_zero_iff_isIso {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    HasLogDeg f 0 ↔ IsIso f := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨a, f', h1, h2⟩ := hf
    have hs : Function.Surjective (f.app (N + a)) :=
      (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A (N + a)) (H.A (N + a)) (f.app (N + a))).2
        ((hN (N + a) (Nat.le_add_right N a)).trans (pow_zero p))
    set f'' : H ⟶ G := (p : ℤ_[p]) ^ N • f' with hf''
    have e1 : f ≫ f'' = (p : ℤ_[p]) ^ (N + a) • 𝟙 G := by
      rw [hf'', Linear.comp_smul, h1, smul_smul, ← pow_add]
    have e2 : f'' ≫ f = (p : ℤ_[p]) ^ (N + a) • 𝟙 H := by
      rw [hf'', Linear.smul_comp, h2, smul_smul, ← pow_add]
    have hc : f''.conv (N + a) = 1 := by
      have h3 : precomp (H.A (N + a)) (f.app (N + a)) (f''.conv (N + a)) =
          precomp (H.A (N + a)) (f.app (N + a)) 1 := by
        rw [map_one, ← comp_conv_left, e2, pow_smul_conv]
      refine WithConv.ofConv_injective (BialgHom.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := hs x
      exact DFunLike.congr_fun (congrArg WithConv.ofConv h3) y
    obtain ⟨g, hg⟩ := GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k H G (N + a) f'' hc
    refine ⟨⟨g, ?_, ?_⟩⟩
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.comp_smul, ← hg, e1]
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.smul_comp, ← hg, e2]
  · intro hi
    refine ⟨0, fun n _ => ?_⟩
    rw [pow_zero]
    refine (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A n) (H.A n) (f.app n)).1 fun x => ⟨(inv f).app n x, ?_⟩
    have h := congrArg (fun φ : G ⟶ G => φ.app n x) (IsIso.hom_inv_id f)
    exact h

theorem isog_basics : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k),
    (∀ m : ℕ, IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) ∧ HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog g → IsIsog (f ≫ g)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog (f ≫ g) → IsIsog g) ∧
    ∀ (H : PDivGroup p k) (f : G ⟶ H), IsIsog f → (HasLogDeg f 0 ↔ IsIso f) :=
  fun _ _ _ _ _ G => ⟨fun m => ⟨isIsog_pow_smul_id G m, hasLogDeg_pow_smul_id G m⟩,
    fun _ _ _ _ => isIsog_comp, fun _ _ _ _ => isIsog_of_comp,
    fun _ f => hasLogDeg_zero_iff_isIso f⟩

end

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTrans

section Pull

variable {X Y Z : Scheme.{0}}

theorem pbT_pbT (T : Z ⟶ Y) (S : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ S ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ T ⁻¹ᵁ O₁) (s : Γ(X, O₀)) : pbT T (pbT S s O₁) O₂ = pbT (T ≫ S) s O₂ := by
  rw [GlobalTheory.KS.pbT_of_le S h₁, GlobalTheory.KS.pbT_of_le T h₂, GlobalTheory.KS.pbT_of_le (T ≫ S) (h₂.trans (T.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE T S O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : pbT (𝟙 Z) s O = rsT s O := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 Z) h, GlobalTheory.KS.rsT_of_le h]
  simp [Scheme.Hom.appLE]
  rfl

theorem pbT_pow (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) (k : ℕ) :
    pbT f (s ^ k) O = pbT f s O ^ k := by
  rw [GlobalTheory.KS.pbT_of_le f h, GlobalTheory.KS.pbT_of_le f h, map_pow]

end Pull

def conjF {Z : Scheme.{0}} (T S : Z ⟶ Z) (d : Fld Z) : Fld Z :=
  fun O f => pbT T (d (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O

section Tr

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]

def tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : G.left ⟶ G.left := (𝟙 G * (toUnit G ≫ x)).left

theorem tr_over (x : 𝟙_ (Over (Sp R)) ⟶ G) : (𝟙 G * (toUnit G ≫ x)) ≫ (𝟙 G * (toUnit G ≫ x⁻¹)) = 𝟙 G := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((𝟙 G * (toUnit G ≫ x)) ≫ toUnit G) (toUnit G),
    _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one]

theorem tr_tr_inv (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ tr G x⁻¹ = 𝟙 _ := by
  rw [tr, tr, ← Over.comp_left, tr_over]; rfl

theorem tr_inv_tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x⁻¹ ≫ tr G x = 𝟙 _ := by
  have := tr_tr_inv G x⁻¹
  rwa [inv_inv] at this

theorem tr_hom (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ G.hom = G.hom := by
  rw [tr]; exact (Over.w _)

end Tr

section Field

variable {Z : Scheme.{0}}

theorem rsT_natCast {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Z, O₀)) O = m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_natCast]

theorem rsT_ofNat {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) [m.AtLeastTwo] :
    rsT (OfNat.ofNat m : Γ(Z, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_ofNat]

theorem rsT_pow {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) (m : ℕ) : rsT (s ^ m) O = rsT s O ^ m := by
  rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h, map_pow]

theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) {W : G.left.Opens} (d : Fld G.left)
    (hd : IsField W d) (p p' : Γ(G.left, W)) (k : ℕ) {O O' : G.left.Opens} (h : O' ≤ O) (hO : O ≤ W)
    (f : Γ(G.left, O)) : op G dd Θ u d p p' k O' (rsT f O') = rsT (op G dd Θ u d p p' k O f) O' := by
  have e1 : ∀ a (g : Γ(G.left, O)), dd a O' (rsT g O') = rsT (dd a O g) O' := fun a g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact (hdd a).2.2 O O' h le_top g
  have e2 : ∀ g : Γ(G.left, O), d O' (rsT g O') = rsT (d O g) O' := fun g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact hd.2.2 O O' h hO g
  simp only [op, GlobalTheory.KS.rsT_add, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_sum, e1, e2,
    GlobalTheory.KS.rsT_constFn _ h, GlobalTheory.KS.rsT_rsT hO h, rsT_natCast h, rsT_ofNat h, rsT_pow h]

end Field

section Conj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem isLift_conjF (D : R → R) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom) (hS : S ≫ G.hom = G.hom) {W : G.left.Opens} {d : Fld G.left} (hl : IsLift G D W d) :
    IsLift G D (T ⁻¹ᵁ W) (conjF T S d) := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hSO : ∀ O, O ≤ T ⁻¹ᵁ W → S ⁻¹ᵁ O ≤ W := fun O hO => (S.preimage_mono hO).trans (hpre W).le
  have back : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := fun O f => by
    rw [pbT_pbT T S le_rfl (hpre' O).ge, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  refine ⟨⟨fun O hO f f' => ?_, fun O hO f f' => ?_, fun O O' hle hO f => ?_⟩, fun O hO r => ?_⟩
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_add, hl.1.1 _ (hSO O hO), GlobalTheory.KS.pbT_add]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_mul, hl.1.2.1 _ (hSO O hO), GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_mul, back, back]
  · simp only [conjF]
    have hS' : S ⁻¹ᵁ O' ≤ S ⁻¹ᵁ O := S.preimage_mono hle
    rw [← GlobalTheory.KS.rsT_of_le hle, ← GlobalTheory.KS.rsT_of_le hle, GlobalTheory.KS.pbT_rsT S hle le_rfl,
      ← GlobalTheory.KS.rsT_pbT S le_rfl hS', GlobalTheory.KS.rsT_of_le hS', hl.1.2.2 _ _ hS' (hSO O hO), ← GlobalTheory.KS.rsT_of_le hS',
      GlobalTheory.KS.pbT_rsT T hS' (hpre' O').ge, GlobalTheory.KS.rsT_pbT T (hpre' O).ge hle]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_constFn _ S le_rfl, hS, hl.2 _ (hSO O hO), GlobalTheory.KS.pbT_constFn _ T (hpre' O).ge, hT]

end Conj

section OpConj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem pbT_natCast {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ) :
    pbT f (m : Γ(Y, O₀)) O = m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_natCast]

theorem pbT_ofNat {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ)
    [m.AtLeastTwo] : pbT f (OfNat.ofNat m : Γ(Y, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_ofNat]

theorem op_conjF {n : ℕ} (dd : Fin n → Fld G.left) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom)
    (hdd : ∀ a (O O' : G.left.Opens), O' ≤ T ⁻¹ᵁ O → ∀ f : Γ(G.left, O), dd a O' (pbT T f O') = pbT T (dd a O f) O')
    (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    {O : G.left.Opens} (hO : O ≤ T ⁻¹ᵁ W) (f : Γ(G.left, O)) :
    op G dd Θ u (conjF T S d) (pbT T p (T ⁻¹ᵁ W)) (pbT T p' (T ⁻¹ᵁ W)) k O f =
      pbT T (op G dd Θ u d p p' k (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hOO : O ≤ T ⁻¹ᵁ (S ⁻¹ᵁ O) := (hpre' O).ge
  have hSO : S ⁻¹ᵁ O ≤ W := (S.preimage_mono hO).trans (hpre W).le
  have back : pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := by
    rw [pbT_pbT T S le_rfl hOO, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  have e : ∀ a (X : Γ(G.left, S ⁻¹ᵁ O)), pbT T (dd a (S ⁻¹ᵁ O) X) O = dd a O (pbT T X O) :=
    fun a X => (hdd a _ _ hOO X).symm
  have ep : ∀ q : Γ(G.left, W), pbT T (rsT q (S ⁻¹ᵁ O)) O = rsT (pbT T q (T ⁻¹ᵁ W)) O := fun q => by
    rw [GlobalTheory.KS.pbT_rsT T hSO hOO, GlobalTheory.KS.rsT_pbT T le_rfl hO]
  simp only [op, conjF, GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_sum, e, ep, back,
    GlobalTheory.KS.pbT_constFn _ T hOO, hT, pbT_natCast T hOO, pbT_ofNat T hOO, pbT_pow T hOO]

end OpConj

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) : tr Y.H x ≫ Y.q.left = Y.q.left ≫ tr Q.P.A (x ≫ Y.q) := by
  have := Y.q_linear.isMonHom
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc, ← Category.assoc,
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg CommaMorphism.left e

theorem preimage_tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (V : Q.P.A.left.Opens) :
    tr Y.H x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) = Y.q.left ⁻¹ᵁ (tr Q.P.A (x ≫ Y.q) ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, tr_q, Scheme.Hom.comp_preimage]

end Ray

end GlobalTheory.HeatTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackLineBundleAutomorphismEqConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAutConst

theorem main : ∀ {A : Type} [CommRing A] (B' : Over (Sp A)) [GrpObj B'] {X : Scheme.{0}} (L : LB X) (π : B'.left ⟶ X), IsAbelianScheme B' → L.IsLB → ∀ w : LB.Iso (L.pull π) (L.pull π), w.IsGen → ∃ lam : Aˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (z : Z) (j : L.ι), π (x z) ∈ L.U j → gm x z _ (w.s (fun _ => j, fun _ => j)) = gm (x ≫ B'.hom) z ⊤ (unitOn lam) := by
  intro A _ B' _ X L π hB hL w hw
  have hP := (isGen_iff w).1 hw
  have hg : ∀ (j j' : L.ι) (x : B'.left), π x ∈ L.U j → π x ∈ L.U j' →
      gm (𝟙 B'.left) x _ ((L.pull π).g (fun _ => j) (fun _ => j')) = gm (𝟙 _ ≫ π) x _ (L.g j j') := by
    intro j j' x hj hj'
    have hp : (𝟙 B'.left : B'.left ⟶ B'.left) x ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    show gm _ x _ (∏ _k : PUnit, (res _ (pullU π _ (L.g j j'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ x _ hp _).trans (gm_pull _ π x (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)
  obtain ⟨u, hu⟩ := glue_unit (⊤ : B'.left.Opens)
    (fun j : L.ι => (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (π x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, mem_pull.2 hj, mem_pull.2 hj⟩)
    (fun j => w.s (fun _ => j, fun _ => j)) (fun j j' x hx => by
      have hj : π x ∈ L.U j := mem_pull.1 hx.1.1
      have hj' : π x ∈ L.U j' := mem_pull.1 hx.2.1
      have e := hP _ (𝟙 _) x j j' (fun _ => j) (fun _ => j') hj hj' (mem_pull.2 hj) (mem_pull.2 hj')
      rw [hg j j' x hj hj', mul_inv_cancel] at e
      exact e.trans (_root_.one_mul _))
  let e₁ : Γ(Sp A, ⊤) ≃+* Γ(B'.left, ⊤) :=
    RingEquiv.ofBijective B'.hom.appTop.hom (GlobalTheory.globalFns_holds _ B' hB)
  let e₂ : A ≃+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let e : A ≃+* Γ(B'.left, ⊤) := e₂.trans e₁
  refine ⟨Units.map e.symm.toMonoidHom u, fun Z x z j hj => ?_⟩
  have hl : pullU B'.hom ⊤ (unitOn (Units.map e.symm.toMonoidHom u)) = u :=
    Units.ext (e.apply_symm_apply u.val)
  have hm : x z ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j) := ⟨mem_pull.2 hj, mem_pull.2 hj⟩
  refine (congrArg (gm x z _) (hu j)).symm.trans ((gm_res x z _ hm _).trans ?_)
  exact (congrArg (gm x z ⊤) hl).symm.trans (gm_pull x B'.hom z ⊤ trivial _)

end GlobalTheory.PullAutConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.TermWt

theorem isWt_term : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hV
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hV' : V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U j := hV
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ V → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b V (rsT (τ.f j) V))) =
        gs b z (LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j) (τ.f j) := by
    intro b hb z
    rw [valR, dif_pos hb, Iso.hom_inv_id_apply, rsT, dif_pos hV']
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z V (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hV (hb trivial) _
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, hJj⟩ := exists_good Q.P.L hL z (fun _ : Fin 1 => x.left ≫ Y.q.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b))
    (fun i => Set.mem_iInter.1 (hV (hV₁ (show z ∈ (⊤ : (Sp S).Opens) from trivial))) i)
  have e₁ : ∀ i, J (x.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := hJj
  have e₂ : ∀ i, J (x'.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := fun i => by rw [hqq]; exact hJj i
  have t₁ := hT (Over.mk (spMap φ)) x z J hJ
  have t₂ := hT (Over.mk (spMap φ)) x' z J hJ
  rw [sval_of τ _ z J j e₁] at t₁
  rw [sval_of τ _ z J j e₂, hq, hc α z J hJ, Units.val_mul] at t₂
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [germ _ hV₂ z, t₂, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, t₁,
    show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.Heat.TermWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermLocalFunctionIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat

theorem isWt_rsT_of_isTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hVj S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hle : Y.q.left ⁻¹ᵁ V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U fun _ => j :=
    fun z hz => Set.mem_iInter.2 fun _ => hVj hz
  have hql : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    have := congrArg CommaMorphism.left hq
    simpa using this

  have key : ((x'.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV').hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) =
      (show Γ((Over.mk (spMap φ)).left, ⊤) from (unitOn (c α)).val) * (x.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV).hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
    refine fn_ext fun y _ => ?_
    have hy : x.left y ∈ Y.q.left ⁻¹ᵁ V := hV trivial
    have hy' : x'.left y ∈ Y.q.left ⁻¹ᵁ V := hV' trivial
    obtain ⟨J, hJ, eJ⟩ := exists_good Q.P.L Q.P.isLB y (fun _ : Unit => x.left ≫ Y.q.left) (fun _ => j)
      (fun _ _ _ => rfl) (fun _ => hVj hy)
    have e := hT _ x' y J hJ
    have e0 := hT _ x y J hJ
    rw [hq, hc α y J hJ] at e
    rw [gs_mul (𝟙 _) y ⊤ trivial, gs_unit (𝟙 _) y ⊤ trivial, gs_appLE _ _ ⊤ _ (𝟙 _) y trivial,
      gs_appLE _ _ ⊤ _ (𝟙 _) y trivial, Category.id_comp, Category.id_comp]
    simp only [rsT, dif_pos hle]
    erw [gs_res _ y hle hy, gs_res _ y hle hy']
    have e1 := sval_of τ x'.left y J (fun _ => j) (fun _ => (congrArg J hql).trans (eJ ()))
    have e2 := sval_of τ x.left y J (fun _ => j) (fun _ => eJ ())
    rw [e1] at e
    rw [e2] at e0
    refine e.trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t) e0.symm)
    simp only [Units.val_mul]
    ring
  unfold valR
  rw [dif_pos hV, dif_pos hV', key, map_mul]
  congr 1
  simp [unitOn]

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusWeightScalarZeroCharacterEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem weight_scalar_zero_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ), x' ≫ Y.q = x ≫ Y.q → (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) → c 0 = 1 := by
  intro R _ _ Q O _ _ _ oa Y S _ φ x x' c _ h
  have e : unitOn (c 0) = unitOn (1 : Sˣ) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext (X := (Over.mk (spMap φ)).left) (V := ⊤) fun y _ => ?_
    choose J hJ using fun ψ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left =>
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart Q.P.isLB (ψ y)
    have hG : Good Q.P.L y J := hJ
    have h0 := h 0 y J hG
    rw [val_corr hG (Y.Φ _ x').s_zero, val_corr hG (Y.Φ _ x).s_zero, val_one, _root_.mul_one] at h0
    have h1 : unitOn (1 : Sˣ) = 1 := map_one _
    exact h0.symm.trans ((congrArg (gm _ y ⊤) h1).trans (map_one _)).symm
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    (congrArg Units.val e))

end GlobalTheory.Heat
end

