import Mathlib
import GroundTheory.TateCohomology.Bundle0003
import GroundTheory.TateCohomology.TateLow
import GroundTheory.TateCohomology.Bundle0002

-- bundled from GroundTheory.TateCohomology.CupConnecting
section
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G]

section Whisker

variable {A A' B B' : Rep k G} {p q n : ℕ}

theorem whiskerRight_tmul (φ : A ⟶ A') (a : A) (b : B) :
    (φ ▷ B).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = φ.hom a ⊗ₜ[k] b :=
  rfl

theorem whiskerLeft_tmul (ψ : B ⟶ B') (a : A) (b : B) :
    (A ◁ ψ).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = a ⊗ₜ[k] ψ.hom b :=
  rfl

theorem whiskerRight_cupCochain (φ : A ⟶ A') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ▷ B).hom (cupCochain h f g x) = cupCochain h (fun v => φ.hom (f v)) g x := by
  rw [cupCochain_apply, whiskerRight_tmul, cupCochain_apply]

theorem whiskerLeft_cupCochain (ψ : B ⟶ B') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (A ◁ ψ).hom (cupCochain h f g x) = cupCochain h f (fun v => ψ.hom (g v)) x := by
  rw [cupCochain_apply, whiskerLeft_tmul, cupCochain_apply, Rep.hom_comm_apply]

end Whisker

section Connecting

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

theorem comp_d_apply {A A' : Rep k G} (φ : A ⟶ A') (i : ℕ) (y : (Fin i → G) → A)
    (v : Fin (i + 1) → G) :
    φ.hom ((inhomogeneousCochains.d A i).hom y v) =
      (inhomogeneousCochains.d A' i).hom (fun u => φ.hom (y u)) v := by
  simp only [inhomogeneousCochains.d_hom_apply, map_add, map_sum, map_smul, Rep.hom_comm_apply]

include hX in

theorem δ_π_eq {p : ℕ} (z : cocycles X.X₃ p) (y : (Fin p → G) → X.X₂)
    (hy : ∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) (x : cocycles X.X₁ (p + 1))
    (hx : ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) = (inhomogeneousCochains.d X.X₂ p).hom y v) :
    δ hX p (p + 1) rfl (π X.X₃ p z) = π X.X₁ (p + 1) x := by
  have h1 := δ_apply hX rfl (iCocycles X.X₃ p z) (by simpa using d_iCocycles z) y
    (funext hy) (iCocycles X.X₁ (p + 1) x) (funext fun v => by simpa using hx v)
  have e1 : cocyclesMk (iCocycles X.X₃ p z) (d_iCocycles z) = z := cocycles_ext (iCocycles_mk _ _)
  rw [e1] at h1
  rw [h1]
  congr 1
  exact cocycles_ext (iCocycles_mk _ _)

include hX in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem exists_f_eq_of_g_eq_zero (e : X.X₂) (he : X.g.hom e = 0) : ∃ a : X.X₁, X.f.hom a = e := by
  have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hmem : e ∈ LinearMap.range X.f.hom.toLinearMap := this ▸ LinearMap.mem_ker.2 he
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩

include hX in

theorem exists_lift_of_cocycle {p : ℕ} (z : cocycles X.X₃ p) :
    ∃ (y : (Fin p → G) → X.X₂) (x : cocycles X.X₁ (p + 1)),
      (∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) ∧
        ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) =
          (inhomogeneousCochains.d X.X₂ p).hom y v := by
  have hg : Function.Surjective X.g.hom := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective X.f).1 hX.mono_f
  choose y hy using fun v => hg (iCocycles X.X₃ p z v)
  have hdy : ∀ v, X.g.hom ((inhomogeneousCochains.d X.X₂ p).hom y v) = 0 := fun v => by
    rw [comp_d_apply, show (fun u => X.g.hom (y u)) = iCocycles X.X₃ p z from funext hy,
      d_iCocycles]
    rfl
  choose x hx using fun v => exists_f_eq_of_g_eq_zero hX _ (hdy v)
  have hdx : (inhomogeneousCochains.d X.X₁ (p + 1)).hom x = 0 := by
    funext v
    apply hf
    rw [comp_d_apply, show (fun u => X.f.hom (x u)) = (inhomogeneousCochains.d X.X₂ p).hom y
      from funext hx, Pi.zero_apply, map_zero]
    exact congr(($(inhomogeneousCochains.d_comp_d (n := p) (A := X.X₂))).hom y v)
  exact ⟨y, cocyclesMk x hdx, hy, fun v => by rw [iCocycles_mk]; exact hx v⟩

variable (B : Rep k G)

theorem δ_cupH_left (hXB : (X.map (tensorRight B)).ShortExact) {p q n : ℕ} (h : p + q = n)
    (h' : p + 1 + q = n + 1) (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n (n + 1) rfl (cupH h a b) = cupH h' (δ hX p (p + 1) rfl a) b := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π]
  subst h
  refine δ_π_eq hXB (cupCocycles rfl z w) (cupCochain rfl y (iCocycles B q w)) (fun v => ?_)
    (cupCocycles h' x w) (fun v => ?_)
  · change (X.g ▷ B).hom (cupCochain rfl y (iCocycles B q w) v) =
      iCocycles (X.X₃ ⊗ B) (p + q) (cupCocycles rfl z w) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain]
    exact congrArg (fun f => cupCochain rfl f (iCocycles B q w) v) (funext hy)
  · change (X.f ▷ B).hom (iCocycles (X.X₁ ⊗ B) (p + q + 1) (cupCocycles h' x w) v) =
      (inhomogeneousCochains.d (X.X₂ ⊗ B) (p + q)).hom (cupCochain rfl y (iCocycles B q w)) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain, d_cupCochain, d_iCocycles,
      cupCochain_zero_right, smul_zero, add_zero]
    exact congrArg (fun f => cupCochain h' f (iCocycles B q w) v) (funext hx)

theorem δ_cupH_right (hBX : (X.map (tensorLeft B)).ShortExact) {p q n : ℕ} (h : q + p = n)
    (h' : q + (p + 1) = n + 1) (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n (n + 1) rfl (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p (p + 1) rfl a) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π, ← map_smul]
  subst h
  refine δ_π_eq hBX (cupCocycles rfl w z) (cupCochain rfl (iCocycles B q w) y) (fun v => ?_)
    ((-1 : k) ^ q • cupCocycles h' w x) (fun v => ?_)
  · change (B ◁ X.g).hom (cupCochain rfl (iCocycles B q w) y v) =
      iCocycles (B ⊗ X.X₃) (q + p) (cupCocycles rfl w z) v
    rw [iCocycles_cupCocycles, whiskerLeft_cupCochain]
    exact congrArg (fun f => cupCochain rfl (iCocycles B q w) f v) (funext hy)
  · change (B ◁ X.f).hom
        (iCocycles (B ⊗ X.X₁) (q + p + 1) ((-1 : k) ^ q • cupCocycles h' w x) v) =
      (inhomogeneousCochains.d (B ⊗ X.X₂) (q + p)).hom (cupCochain rfl (iCocycles B q w) y) v
    rw [map_smul, Pi.smul_apply, map_smul, iCocycles_cupCocycles, whiskerLeft_cupCochain,
      d_cupCochain, d_iCocycles, cupCochain_zero_left, zero_add, Pi.smul_apply]
    exact congrArg (fun f => (-1 : k) ^ q • cupCochain h' (iCocycles B q w) f v) (funext hx)

theorem δ_cupH_left' (hXB : (X.map (tensorRight B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : p + q = n) (h' : p' + q = m)
    (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n m hm (cupH h a b) = cupH h' (δ hX p p' hp a) b := by
  subst hp hm
  exact δ_cupH_left hX B hXB h h' a b

theorem δ_cupH_right' (hBX : (X.map (tensorLeft B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : q + p = n) (h' : q + p' = m)
    (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n m hm (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p p' hp a) := by
  subst hp hm
  exact δ_cupH_right hX B hBX h h' b a

end Connecting

end GroundTheory.GroupCoh
end
end

-- bundled from GroundTheory.TateCohomology.CupFunctorial
section
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep

namespace GroundTheory.GroupCoh

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem partialProd_comp {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {m : ℕ}
    (x : Fin m → M) (i : Fin (m + 1)) :
    Fin.partialProd (f ∘ x) i = f (Fin.partialProd x i) := by
  simp [Fin.partialProd, ← List.map_ofFn, ← List.map_take, map_list_prod]

variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}

def resTensorHom (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) : res f (A₁ ⊗ A₂) ⟶ B₁ ⊗ B₂ :=
  ConcreteCategory.ofHom (C := Rep k G)
    { toLinearMap := TensorProduct.map φ₁.hom.toLinearMap φ₂.hom.toLinearMap
      isIntertwining' := fun g => TensorProduct.ext' fun a b => by
        change φ₁.hom (A₁.ρ (f g) a) ⊗ₜ[k] φ₂.hom (A₂.ρ (f g) b) =
          B₁.ρ g (φ₁.hom a) ⊗ₜ[k] B₂.ρ g (φ₂.hom b)
        rw [← Rep.hom_comm_apply φ₁, ← Rep.hom_comm_apply φ₂]
        rfl }

theorem resTensorHom_tmul (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (a : A₁) (b : A₂) :
    (resTensorHom f φ₁ φ₂).hom (a ⊗ₜ[k] b : (A₁ ⊗ A₂ : Rep k H)) = φ₁.hom a ⊗ₜ[k] φ₂.hom b :=
  rfl

theorem resTensorHom_cupCochain (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (x : (Fin p → H) → A₁) (y : (Fin q → H) → A₂) (g : Fin n → G) :
    (resTensorHom f φ₁ φ₂).hom (cupCochain h x y (f ∘ g)) =
      cupCochain h (fun v => φ₁.hom (x (f ∘ v))) (fun v => φ₂.hom (y (f ∘ v))) g := by
  rw [cupCochain_apply, resTensorHom_tmul, cupCochain_apply, partialProd_comp]
  exact congrArg _ (Rep.hom_comm_apply φ₂ _ _)

theorem map_π_apply' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (z : cocycles A n) :
    map f φ n (π A n z) = π B n (cocyclesMap f φ n z) := by
  change (π A n ≫ map f φ n).hom z = (cocyclesMap f φ n ≫ π B n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B)
    (z : cocycles A n) :
    iCocycles B n (cocyclesMap f φ n z) = fun g => φ.hom (iCocycles A n z (f ∘ g)) := by
  change (cocyclesMap f φ n ≫ iCocycles B n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_resTensorHom_cupH (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (a : groupCohomology A₁ p) (b : groupCohomology A₂ q) :
    map f (resTensorHom f φ₁ φ₂) n (cupH h a b) = cupH h (map f φ₁ p a) (map f φ₂ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A₁ ⊗ A₂) f (resTensorHom f φ₁ φ₂) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap f φ₁ p z) (cocyclesMap f φ₂ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap', iCocycles_cupCocycles, iCocycles_cupCocycles,
      iCocycles_cocyclesMap', iCocycles_cocyclesMap']
    funext g
    exact resTensorHom_cupCochain f φ₁ φ₂ h _ _ g
  rw [cupH_π, map_π_apply', map_π_apply', map_π_apply', cupH_π, key]

end GroundTheory.GroupCoh
end
end

-- bundled from GroundTheory.TateCohomology.HerbrandTate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory

theorem natCard_kerModRange_eq_relIndex {A : Type*} [AddCommGroup A] (f g : A →+ A) :
    Nat.card (KerModRange f g) = g.range.relIndex f.ker :=
  rfl

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

omit [Fintype G] in

theorem ker_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, repSubOne_apply, sub_eq_zero, Submodule.mem_toAddSubgroup,
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ]

theorem range_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ]
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem ker_repNorm (A : Rep.{u} R G) :
    (repNorm A).ker = (LinearMap.ker A.ρ.norm).toAddSubgroup :=
  rfl

theorem range_repNorm (A : Rep.{u} R G) :
    (repNorm A).range = (LinearMap.range A.ρ.norm).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem natCard_tateCohomology_zero (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A 0) = Nat.card (KerModRange (repSubOne A σ) (repNorm A)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repSubOne A hσ, range_repNorm]
  exact Nat.card_congr ((tateCohomologyZeroIso R G).app A).toLinearEquiv.toEquiv

theorem natCard_tateCohomology_neg_one (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A (-1)) = Nat.card (KerModRange (repNorm A) (repSubOne A σ)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repNorm, range_repSubOne A hσ]
  exact Nat.card_congr ((tateCohomologyNegOneIso R G).app A).toLinearEquiv.toEquiv

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.PGroupFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra

universe u

section Naturality

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (f : A ⟶ B)

theorem d₁₀_mapRange (y : G →₀ A) :
    d₁₀ B (Finsupp.mapRange.linearMap f.hom.toLinearMap y) = f.hom (d₁₀ A y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₁₀_single, d₁₀_single,
      map_sub, Rep.hom_comm_apply]
    rfl

theorem d₂₁_mapRange (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange.linearMap f.hom.toLinearMap c) =
      Finsupp.mapRange.linearMap f.hom.toLinearMap (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₂₁_single, d₂₁_single,
      map_add, map_sub, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single,
      show f.hom.toLinearMap (A.ρ g.1⁻¹ a) = B.ρ g.1⁻¹ (f.hom.toLinearMap a) from
        Rep.hom_comm_apply f g.1⁻¹ a]

end Naturality

section Chains

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}

theorem d₁₀_apply_eq_sum (z : G →₀ A) :
    d₁₀ A z = ∑ g ∈ z.support, (A.ρ g⁻¹ (z g) - z g) := by
  change (Finsupp.lsum k fun g => A.ρ g⁻¹ - LinearMap.id) z = _
  rw [Finsupp.lsum_apply, Finsupp.sum]
  rfl

theorem exists_chain_ker_of_isZero_groupHomology_one (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1)) {x : A}
    (hx : f.hom x = 0) (hxI : x ∈ Coinvariants.ker A.ρ) :
    ∃ z : G →₀ A, (∀ g, f.hom (z g) = 0) ∧ d₁₀ A z = x := by
  have hsurj' : Function.Surjective f.hom.toLinearMap := hsurj
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (d₁₀ A).hom := by
    rw [range_d₁₀_eq_coinvariantsKer]
    exact hxI
  let L := Finsupp.mapRange.linearMap (α := G) f.hom.toLinearMap
  have hY : L y ∈ cycles₁ B := by
    change d₁₀ B (L y) = 0
    rw [d₁₀_mapRange f y]
    change f.hom (d₁₀ A y) = 0
    rw [show d₁₀ A y = x from hy]
    exact hx
  have h0 : H1π B ⟨L y, hY⟩ = 0 :=
    @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hB) _ _
  obtain ⟨c, hc⟩ := (H1π_eq_zero_iff _).mp h0
  obtain ⟨c', rfl⟩ := Finsupp.mapRange_surjective f.hom.toLinearMap (map_zero _) hsurj' c
  refine ⟨y - d₂₁ A c', fun g => ?_, ?_⟩
  · have h2 : L (d₂₁ A c') = L y := (d₂₁_mapRange f c').symm.trans hc
    have h4 : L (y - d₂₁ A c') = 0 := by
      have h5 : L (y - d₂₁ A c') = L y - L (d₂₁ A c') := map_sub L y _
      rw [h5, h2, sub_self]
    have := congrArg (fun w => w g) h4
    simpa [L] using this
  · have h3 : d₁₀ A (d₂₁ A c') = 0 := by simp
    have h5 : d₁₀ A (y - d₂₁ A c') = d₁₀ A y - d₁₀ A (d₂₁ A c') := map_sub (d₁₀ A).hom y _
    rw [h5, h3, sub_zero]
    exact hy

end Chains

section PGroup

variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]

theorem injective_of_isZero_groupHomology_one (hG : IsPGroup p G) {A B : Rep.{u} k G} (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1))
    (hker : ∀ x, f.hom x = 0 → x ∈ Coinvariants.ker A.ρ) : Function.Injective f.hom := by
  let K := LinearMap.ker f.hom.toLinearMap
  have hK : ∀ g, K ≤ K.comap (A.ρ g) := fun g x hx => by
    have hx' : f.hom x = 0 := LinearMap.mem_ker.mp hx
    refine LinearMap.mem_ker.mpr ?_
    change f.hom (A.ρ g x) = 0
    rw [Rep.hom_comm_apply, hx', map_zero]
  let ρK : @Representation k G K _ _ AddCommGroup.toAddCommMonoid _ := A.ρ.subrepresentation K hK
  have hKI : Coinvariants.ker (k := k) (G := G) (V := K) ρK = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx0 : f.hom x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨z, hz, hdz⟩ := exists_chain_ker_of_isZero_groupHomology_one f hsurj hB hx0 (hker x hx0)
    have hzK : ∀ g, z g ∈ K := fun g => LinearMap.mem_ker.mpr (hz g)
    have hmem : (⟨x, hx⟩ : K) = ∑ g ∈ z.support, (ρK g⁻¹ ⟨z g, hzK g⟩ - ⟨z g, hzK g⟩) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change x = _
      rw [← hdz, d₁₀_apply_eq_sum]
      rfl
    rw [hmem]
    exact Submodule.sum_mem _ fun g _ => Coinvariants.sub_mem_ker g⁻¹ _
  have hKs : Subsingleton K := by
    apply subsingleton_of_coinvariantsKer_eq_top hG ρK
    exact hKI
  intro x y hxy
  have hxy' : x - y ∈ K := LinearMap.mem_ker.mpr (by
    change f.hom (x - y) = 0
    rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp (congrArg Subtype.val (Subsingleton.elim (⟨x - y, hxy'⟩ : K) 0))

theorem exists_iso_free_of_isZero_groupHomology_one (hG : IsPGroup p G) (M : Rep.{u} k G)
    (hM : IsZero (groupHomology M 1)) : ∃ ι : Type u, Nonempty (Rep.free k G ι ≅ M) := by
  classical

  let ι := Module.Free.ChooseBasisIndex k (Coinvariants M.ρ)
  let b : Module.Basis ι k (Coinvariants M.ρ) := Module.Free.chooseBasis k (Coinvariants M.ρ)
  choose e he using fun i => Coinvariants.mk_surjective M.ρ (b i)
  let π : Rep.free k G ι ⟶ M := Rep.freeLift (k := k) (G := G) (A := M) e
  have hπ : ∀ i g r, π.hom (single i (MonoidAlgebra.single g r)) = r • M.ρ g (e i) :=
    fun i g r => by simp [π]

  have hsurj : Function.Surjective π.hom := by
    have hr : LinearMap.range π.hom.toLinearMap = ⊤ := by
      apply eq_top_of_sup_coinvariantsKer_eq_top hG M.ρ
      · rintro g _ ⟨y, rfl⟩
        exact LinearMap.mem_range.mpr ⟨(Rep.free k G ι).ρ g y, Rep.hom_comm_apply π g y⟩
      · rw [eq_top_iff]
        intro x _
        have hx : Coinvariants.mk M.ρ x ∈ Submodule.span k (Set.range b) :=
          b.span_eq ▸ Submodule.mem_top
        have hmap : Submodule.span k (Set.range b) ≤
            (LinearMap.range π.hom.toLinearMap).map (Coinvariants.mk M.ρ) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact Submodule.mem_map.mpr ⟨e i, LinearMap.mem_range.mpr
            ⟨single i (MonoidAlgebra.single 1 1), by simpa using hπ i 1 1⟩, he i⟩
        obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp (hmap hx)
        have hxw : x - w ∈ Coinvariants.ker M.ρ := (Coinvariants.mk_eq_iff M.ρ).mp hwx.symm
        rw [show x = w + (x - w) by abel]
        exact Submodule.add_mem_sup hw hxw
    exact LinearMap.range_eq_top.mp hr

  let lam : M.V →ₗ[k] (ι →₀ k) := b.repr.toLinearMap ∘ₗ Coinvariants.mk M.ρ
  let s : (ι →₀ k) →ₗ[k] (ι →₀ k[G]) := Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle 1)
  have hlam : ∀ y, y - s (lam (π.hom y)) ∈ Coinvariants.ker (Representation.free k G ι) := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem h₁ h₂
    | single i a =>
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a₁ a₂ h₁ h₂ =>
        rw [Finsupp.single_add, map_add, map_add, map_add, add_sub_add_comm]
        exact add_mem h₁ h₂
      | single g r =>
        refine Coinvariants.mem_ker_of_eq g (single i (MonoidAlgebra.single 1 r)) _ ?_
        rw [hπ]
        simp [lam, s, he]
  have hker : ∀ x, π.hom x = 0 → x ∈ Coinvariants.ker (Rep.free k G ι).ρ := fun x hx => by
    simpa [hx] using hlam x

  have hinj : Function.Injective π.hom :=
    injective_of_isZero_groupHomology_one hG π hsurj hM hker
  let eqv : (Representation.free k G ι).Equiv M.ρ :=
    Representation.Equiv.mk (LinearEquiv.ofBijective π.hom.toLinearMap ⟨hinj, hsurj⟩) fun g =>
      LinearMap.ext fun y => Rep.hom_comm_apply π g y
  exact ⟨ι, ⟨Rep.mkIso eqv⟩⟩

theorem free_asModule_of_iso_free {k G : Type u} [CommRing k] [Group G] {M : Rep.{u} k G}
    {ι : Type u} (e : Rep.free k G ι ≅ M) : Module.Free k[G] M.ρ.asModule := by
  let φ := Representation.equivOfIso e
  have := Representation.free_asModule_free k G ι
  exact Module.Free.of_equiv (LinearEquiv.ofLinearMap
    (IntertwiningMap.equivLinearMapAsModule (ρ := (Rep.free k G ι).ρ) (σ := M.ρ) φ.toIntertwiningMap)
    (IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := (Rep.free k G ι).ρ)
      φ.symm.toIntertwiningMap)
    (LinearMap.ext fun x => φ.apply_symm_apply x) (LinearMap.ext fun x => φ.symm_apply_apply x))

end PGroup

end GroundTheory.GroupCoh
end

