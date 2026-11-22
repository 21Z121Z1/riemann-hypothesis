import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsPerfectOfIsDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3642
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3645
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfValEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TranslChar

variable {S X : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} {L : LB X}
  {K K' : Type} [Fintype K] [Fintype K']

def tr (y : T ⟶ A) : A ⊗ T ⟶ A ⊗ T := lift (fst A T * (snd A T ≫ y)) (snd A T)

@[reassoc] theorem tr_snd (y : T ⟶ A) : tr y ≫ snd A T = snd A T := lift_snd _ _

@[reassoc] theorem tr_fst (y : T ⟶ A) : tr y ≫ fst A T = fst A T * (snd A T ≫ y) := lift_fst _ _

theorem tr_mul (y y' : T ⟶ A) : tr (y * y') = tr y ≫ tr y' := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [tr, Category.assoc, lift_fst, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, _root_.mul_assoc]
  · simp [tr]

theorem tr_whisker {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f] (y : T ⟶ A) :
    tr y ≫ f ▷ T = f ▷ T ≫ tr (y ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [tr, MonObj.mul_comp, MonObj.comp_mul]
  · simp [tr]

theorem tr_one : tr (1 : T ⟶ A) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [tr]

def Ch {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} (σ : LB.Gen (LB.LinComb L φ ε)) (y : T ⟶ A)
    (u : Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (q : Z ⟶ (A ⊗ T).left) (w : Z) (J : (Z ⟶ X) → L.ι), Good L w J →
    val σ (q ≫ (tr y).left) w J = gm (q ≫ (snd A T).left) w ⊤ u * val σ q w J

theorem exists_unit_base (hA : IsAbelianScheme A) (a : Γ((A ⊗ T).left, ⊤)ˣ) :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ (A ⊗ T).left) (w : Z),
      gm q w ⊤ a = gm (q ≫ (snd A T).left) w ⊤ u := by
  have hsurj : Function.Surjective ((snd A T).left.appTop).hom :=
    surjective_app_of_isAbelianScheme SemiRigid.globalFns ((Over.pullback T.hom).obj A)
      (Out.TLinPf.isAb_pullback T.hom A hA) ⊤
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have key : ∀ x, ((lift (1 : T ⟶ A) (𝟙 T)).left.appTop).hom (((snd A T).left.appTop).hom x) = x := by
    intro x
    have := congrArg (fun f : T.left ⟶ T.left => (f.appTop).hom x) he
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_id, RingHom.id_apply] at this
    exact this
  have hinj : Function.Injective ((snd A T).left.appTop).hom := fun x y hxy => by
    rw [← key x, ← key y, hxy]
  obtain ⟨b, hb⟩ := hsurj (a : Γ((A ⊗ T).left, ⊤))
  obtain ⟨b', hb'⟩ := hsurj ((a⁻¹ : Γ((A ⊗ T).left, ⊤)ˣ) : Γ((A ⊗ T).left, ⊤))
  have h1 : b * b' = 1 := hinj (by
    rw [map_mul, map_one, hb, hb']
    simp)
  refine ⟨⟨b, b', h1, by rw [mul_comm, h1]⟩, fun Z q w => ?_⟩
  have hu : pullU (snd A T).left ⊤ ⟨b, b', h1, by rw [mul_comm, h1]⟩ = a := Units.ext hb
  rw [← gm_pull q (snd A T).left w ⊤ trivial, hu]
  rfl

theorem exists_ratio (hL : L.IsLB) {E W : Scheme.{0}} {φ : K → (E ⟶ X)} {ε : K → ℤ}
    (σ : LB.Gen (LB.LinComb L φ ε)) (hσ : σ.IsGen) (r₁ r₀ : W ⟶ E) (h : ∀ k, r₁ ≫ φ k = r₀ ≫ φ k) :
    ∃ a : Γ(W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ W) (w : Z) (J), Good L w J →
      val σ (q ≫ r₁) w J = gm q w ⊤ a * val σ (q ≫ r₀) w J := by
  have gen : ∀ (ψ₁ ψ₀ : K → (W ⟶ X)), ψ₁ = ψ₀ → ∀ (t₁ : (L.LinComb ψ₁ ε).Gen) (t₀ : (L.LinComb ψ₀ ε).Gen),
      t₁.IsGen → t₀.IsGen → ∃ a : Γ(W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ W) (w : Z) (J : (Z ⟶ X) → L.ι),
        Good L w J → val t₁ q w J = gm q w ⊤ a * val t₀ q w J := by
    rintro ψ _ rfl t₁ t₀ h₁ h₀
    exact AbPackage.exists_unit_ratio hL h₁ h₀
  obtain ⟨a, ha⟩ := gen _ _ (funext h) _ _ (DVR.pullGen_isGen L φ ε σ hσ r₁) (DVR.pullGen_isGen L φ ε σ hσ r₀)
  refine ⟨a, fun Z q w J hJ => ?_⟩
  have := ha Z q w J hJ
  rwa [val_pull hJ, val_pull hJ] at this

theorem exists_ch (hA : IsAbelianScheme A) (hL : L.IsLB) {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ}
    (σ : LB.Gen (LB.LinComb L φ ε)) (hσ : σ.IsGen) (y : T ⟶ A) (h : ∀ k, (tr y).left ≫ φ k = φ k) :
    ∃ u, Ch σ y u := by
  obtain ⟨a, ha⟩ := exists_ratio hL σ hσ (tr y).left (𝟙 _) (fun k => by rw [h, Category.id_comp])
  obtain ⟨u, hu⟩ := exists_unit_base hA a
  refine ⟨u, fun Z q w J hJ => ?_⟩
  rw [ha Z q w J hJ, hu, Category.comp_id]

theorem Ch.unique (hL : L.IsLB) {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} {σ : LB.Gen (LB.LinComb L φ ε)}
    {y : T ⟶ A} {u u' : Γ(T.left, ⊤)ˣ} (h : Ch σ y u) (h' : Ch σ y u') : u = u' := by
  apply unit_ext
  intro x _
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hJ : Good L x (fun ψ => (exists_chart hL (ψ x)).choose) := fun ψ => (exists_chart hL (ψ x)).choose_spec
  have h1 := h T.left (lift (1 : T ⟶ A) (𝟙 T)).left x _ hJ
  have h2 := h' T.left (lift (1 : T ⟶ A) (𝟙 T)).left x _ hJ
  have := mul_right_cancel (h1.symm.trans h2)
  rwa [he] at this

theorem Ch.of_formEq (hA : IsAbelianScheme A) (hL : L.IsLB) {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((A ⊗ T).left ⟶ X)} {ε' : K' → ℤ} (hf : FormEq φ ε φ' ε') {σ : LB.Gen (LB.LinComb L φ ε)}
    (hσ : σ.IsGen) {σ' : LB.Gen (LB.LinComb L φ' ε')} (hσ' : σ'.IsGen) {y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ}
    (h : Ch σ y u) : Ch σ' y u := by
  obtain ⟨t', ht', hvt⟩ := exists_gen hL hf σ hσ
  obtain ⟨a, ha⟩ := AbPackage.exists_unit_ratio hL hσ' ht'
  obtain ⟨b, hb⟩ := exists_unit_base hA a
  intro Z q w J hJ
  rw [ha _ _ _ _ hJ, ha _ _ _ _ hJ, hvt _ _ _ _ hJ, hvt _ _ _ _ hJ, h Z q w J hJ, hb, hb,
    Category.assoc, ← Over.comp_left, tr_snd]
  exact mul_left_comm _ _ _

theorem Ch.mul {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((A ⊗ T).left ⟶ X)} {ε' : K' → ℤ}
    {σ : LB.Gen (LB.LinComb L φ ε)} {σ' : LB.Gen (LB.LinComb L φ' ε')} {y : T ⟶ A} {u u' : Γ(T.left, ⊤)ˣ}
    (h : Ch σ y u) (h' : Ch σ' y u') : Ch (LB.mulGen L _ _ _ _ σ σ') y (u * u') := by
  intro Z q w J hJ
  rw [val_mul hJ, val_mul hJ, h Z q w J hJ, h' Z q w J hJ, map_mul]
  exact mul_mul_mul_comm _ _ _ _

theorem Ch.comp {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} {σ : LB.Gen (LB.LinComb L φ ε)} {y y' : T ⟶ A}
    {u u' : Γ(T.left, ⊤)ˣ} (h : Ch σ y u) (h' : Ch σ y' u') : Ch σ (y * y') (u * u') := by
  intro Z q w J hJ
  rw [tr_mul, Over.comp_left, ← Category.assoc, h' Z _ w J hJ, h Z q w J hJ, Category.assoc,
    ← Over.comp_left, tr_snd, map_mul]
  ac_rfl

theorem Ch.one {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} (σ : LB.Gen (LB.LinComb L φ ε)) :
    Ch σ (1 : T ⟶ A) 1 := by
  intro Z q w J hJ
  rw [tr_one, Over.id_left, Category.comp_id, map_one, _root_.one_mul]

theorem Ch.pull {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f] {φ : K → ((B ⊗ T).left ⟶ X)} {ε : K → ℤ}
    {σ : LB.Gen (LB.LinComb L φ ε)} {y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ} (h : Ch σ (y ≫ f) u) :
    Ch (LB.pullGen L _ _ σ (f ▷ T).left) y u := by
  intro Z q w J hJ
  rw [val_pull hJ, val_pull hJ, Category.assoc, ← Over.comp_left, tr_whisker, Over.comp_left,
    ← Category.assoc, h Z _ w J hJ, Category.assoc, ← Over.comp_left, whiskerRight_snd]

theorem gm_id_eq_one {V Z : Scheme.{0}} (i : V ⟶ Z) [IsOpenImmersion i] (w : V) (a : Γ(Z, ⊤)ˣ)
    (h : gm i w ⊤ a = 1) : gm (𝟙 Z) (i w) ⊤ a = 1 := by
  apply Units.ext
  have h1 := congrArg Units.val h
  rw [Units.val_one, gm_val i w ⊤ trivial] at h1
  rw [Units.val_one, gm_val (𝟙 Z) (i w) ⊤ trivial]
  have hinj : Function.Injective (i.stalkMap w).hom :=
    (asIso (i.stalkMap w)).commRingCatIsoToRingEquiv.injective
  apply hinj
  rw [map_one, ← h1]
  simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  exact Scheme.Hom.germ_stalkMap_apply i ⊤ w trivial _

theorem exists_gen_of_val_eq (hL : L.IsLB) {E F : Scheme.{0}} (π : E ⟶ F) (hF : Flat π) (hS : Surjective π)
    (hA : IsAffineHom π) (φ : F ⟶ X) (σ : LB.Gen (L.pull (π ≫ φ))) (hσ : σ.IsGen)
    (hval : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ E), g₁ ≫ π = g₂ ≫ π → ∀ z J, Good L z J → val σ g₁ z J = val σ g₂ z J) :
    ∃ t : (L.pull φ).Gen, t.IsGen := by
  classical
  have hmem : ∀ (j : (L.pull φ).ι) (x : E), x ∈ (L.pull (π ≫ φ)).U j ↔ π x ∈ (L.pull φ).U j := by
    intro j x
    simp [LB.pull, LB.LinComb, LB.wchart]
  have hle : ∀ j : (L.pull φ).ι, π ⁻¹ᵁ (L.pull φ).U j ≤ (L.pull (π ≫ φ)).U j :=
    fun j x hx => (hmem j x).2 hx
  have desc : ∀ j : (L.pull φ).ι, ∃ u : Γ(F, (L.pull φ).U j)ˣ, pullU π _ u = res (hle j) (σ.s j) := by
    intro j
    haveI := hF
    haveI := hS
    haveI := hA
    refine EigenDescent.unit_descends π _ _ ?_
    intro Z g₁ g₂ h₁ h₂ hπ
    have e1 : ∀ (g : Z ⟶ E) (hg : ∀ z, g z ∈ π ⁻¹ᵁ (L.pull φ).U j) (z : Z),
        gm (𝟙 Z) z ⊤ (EigenDescent.evU g hg (res (hle j) (σ.s j))) = gm g z _ (σ.s j) := by
      intro g hg z
      have h0 := gm_res (𝟙 Z) z (U := g ⁻¹ᵁ π ⁻¹ᵁ (L.pull φ).U j) (V := ⊤) (fun x _ => hg x) (by simp)
        (pullU g _ (res (hle j) (σ.s j)))
      refine h0.trans ?_
      rw [gm_pull _ _ _ _ (hg z), Category.id_comp]
      exact gm_res g z (hle j) (hg z) (σ.s j)
    apply unit_ext
    intro z _
    rw [e1, e1]
    let J : (Z ⟶ X) → L.ι := fun ψ =>
      if ψ z ∈ L.U (j PUnit.unit) then j PUnit.unit else (exists_chart hL (ψ z)).choose
    have hJ : Good L z J := by
      intro ψ
      by_cases hψ : ψ z ∈ L.U (j PUnit.unit)
      · simp only [J, if_pos hψ]
        exact hψ
      · simp only [J, if_neg hψ]
        exact (exists_chart hL (ψ z)).choose_spec
    have hj : ∀ (g : Z ⟶ E), g z ∈ π ⁻¹ᵁ (L.pull φ).U j → (fun k : PUnit => J (g ≫ (π ≫ φ))) = j := by
      intro g hg
      funext k
      have hin : (g ≫ π ≫ φ) z ∈ L.U (j PUnit.unit) := by
        have := (hmem j (g z)).2 hg
        simp [LB.pull, LB.LinComb, LB.wchart] at this
        simpa using this PUnit.unit
      simp only [J, if_pos hin]
    have hv := hval Z g₁ g₂ hπ z J hJ
    unfold val at hv
    rw [hj g₁ (h₁ z)] at hv
    try rw [hj g₂ (h₂ z)] at hv
    exact hv
  choose u hu using desc
  refine ⟨⟨u⟩, ?_⟩
  intro i j
  apply EigenDescent.pullU_injective_of_flat_surjective π hF hS
  apply unit_ext
  intro x hx
  have hxi : π x ∈ (L.pull φ).U i := hx.1
  have hxj : π x ∈ (L.pull φ).U j := hx.2
  have hts : ∀ k (hy : π x ∈ (L.pull φ).U k), gm π x _ (u k) = gm (𝟙 E) x _ (σ.s k) := by
    intro k hy
    have h1 := gm_pull (𝟙 E) π x _ hy (u k)
    rw [Category.id_comp] at h1
    rw [← h1, hu k]
    exact gm_res (𝟙 E) x (hle k) hy (σ.s k)
  have hs := congrArg (gm (𝟙 E) x ((L.pull (π ≫ φ)).U i ⊓ (L.pull (π ≫ φ)).U j)) (hσ i j)
  have hxV : (𝟙 E) x ∈ (L.pull (π ≫ φ)).U i ⊓ (L.pull (π ≫ φ)).U j := ⟨hle i hxi, hle j hxj⟩
  rw [map_mul, gm_res _ _ _ hxV, gm_res _ _ _ hxV] at hs
  rw [map_mul, map_mul]
  have hx' : π ((𝟙 E) x) ∈ (L.pull φ).U i ⊓ (L.pull φ).U j := hx
  have hxπ : π x ∈ (L.pull φ).U i ⊓ (L.pull φ).U j := hx
  simp only [gm_pull _ _ _ _ hx', Category.id_comp]
  rw [gm_res _ _ _ hxπ, gm_res _ _ _ hxπ, hts i hxi, hts j hxj, hs]
  congr 1
  have g1 := gm_linComb L (fun _ => π ≫ φ) (fun _ => 1) (𝟙 E) x i j (hle i hxi) (hle j hxj)
  have g2 := gm_linComb L (fun _ => φ) (fun _ => 1) π x i j hxi hxj
  simp only [Category.id_comp] at g1
  exact g1.trans g2.symm

end GlobalTheory.TranslChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESDual

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}

def scaleTate {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {w : ℕ → Q → Q → kˣ → Prop}
    (I : TateIsoO D k Q act w) (e : ℕ) : TateIsoO D k Q act w where
  ζ n := I.ζ n ^ ((p ^ e) ^ 2)
  ζ_prim n hn hp := (I.ζ_prim n hn hp).pow_of_coprime _ ((hp.symm.pow_left e).pow_left 2)
  ζ_pow n m hn hm h := by rw [pow_right_comm, I.ζ_pow n m hn hm h]
  ev n x := I.ev n (p ^ e • x)
  add n x y := by rw [smul_add, I.add]
  lin n c x := by rw [smul_comm, I.lin]
  ker n hn hp x := by
    rw [I.ker n hn hp]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • y + v • x, ?_⟩
      rw [smul_add, smul_comm n u, ← hy, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
        ← add_smul, huv, one_smul]
    · rintro ⟨y, rfl⟩
      exact ⟨p ^ e • y, smul_comm _ _ _⟩
  onto n hn hp q := by
    rw [I.onto n hn hp]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • x, ?_⟩
      have e1 : x = p ^ e • u • x + n • v • x := by
        rw [smul_comm _ u, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
          ← add_smul, huv, one_smul]
      have e2 := (I.ker n hn hp (n • v • x)).2 ⟨_, rfl⟩
      conv_rhs => rw [e1, I.add, e2, _root_.mul_one]
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm h x := I.tower n m hn hm h _
  isom n hn hp x y := by
    have h := I.isom n hn hp (p ^ e • x) (p ^ e • y)
    have e1 : (2 * D.EF (p ^ e • x) (p ^ e • y) : ℤ) = (((p ^ e) ^ 2 : ℕ) : ℤ) * (2 * D.EF x y) := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, zpow_mul, zpow_natCast] at h
    exact h

def scale {s : S ⟶ Sp R} (o : Obj b N s) (e : ℕ) {s' : S ⟶ Sp R} (h : s = s') : Obj b N s' where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie := h ▸ o.lie
  lieRank := h ▸ o.lieRank
  eta x := o.eta (p ^ e • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, o.eta_ker]
  geom k _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom k x β (h ▸ hx)
    exact ⟨scaleTate I e, fun y => hI _⟩

theorem eta_nsmul {s : S ⟶ Sp R} (o : Obj b N s) (n : ℕ) (x : D.La) : o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem eta_congr {s : S ⟶ Sp R} (o : Obj b N s) {n : ℕ} (hn : n ≡ 1 [MOD N]) (hn0 : 0 < n) (x : D.La) :
    o.eta (n • x) = o.eta x := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hn0).1 hn.symm
  have : n = 1 + N * k := by omega
  rw [this, add_smul, one_smul, mul_smul, o.eta_add, o.eta_ker, _root_.mul_one]

theorem exists_inv_exp (hN : 0 < N) (hp : N.Coprime p) (e : ℕ) : ∃ f : ℕ, p ^ (e + f) ≡ 1 [MOD N] := by
  refine ⟨e * (N.totient - 1), ?_⟩
  have h1 : 1 ≤ N.totient := Nat.totient_pos.2 hN
  have : e + e * (N.totient - 1) = N.totient * e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h1
    rw [hm]; simp; ring
  rw [this, pow_mul]
  simpa using (Nat.ModEq.pow_totient hp.symm).pow e

def idMap {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) where
  φ := 𝟙 _
  φ₂ := 𝟙 _
  cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
  sq := ⟨by simp, by simp⟩
  act c := by simp
  pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
  eta y := by simp

def compMap {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := h₁.φ ≫ h₂.φ
  φ₂ := h₁.φ₂ ≫ h₂.φ₂
  cart := h₁.cart.comp h₂.cart
  sq := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  act c := by rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  pol := by
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    exact LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  eta y := by rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]

theorem pow_left_comm {S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : ℕ) :
    ((𝟙 A') ^ c).left ≫ φ = φ ≫ ((𝟙 A) ^ c).left := by
  let u : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (u ^ n).left = ((𝟙 A') ^ n).left ≫ φ := by
    intro n
    induction n with
    | zero =>
      let v : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk ((1 : A' ⟶ A').left ≫ φ) (by
        rw [Category.assoc, h.1.w, Over.w_assoc]; rfl)
      have h1 := h.2 A' 1 1 v v rfl rfl
      rw [_root_.mul_one] at h1
      have h2 : v = 1 := mul_eq_left.1 (Over.OverMorphism.ext h1 : v * v = v)
      rw [pow_zero, pow_zero, ← h2]; rfl
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact h.2 A' _ _ _ _ ih (Category.id_comp _).symm
  rw [← key]
  have : u ^ c = u ≫ (𝟙 A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
  rw [this]; rfl

theorem square_dual {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj A'] [GrpObj B'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hB : IsAbelianScheme B') (φ' : B'.left ⟶ B.left) {c : ℕ}
    (hc : 0 < c) {ψ : A ⟶ B} {χ : B ⟶ A} {ψ' : A' ⟶ B'} {χ' : B' ⟶ A'} (h₁ : ψ ≫ χ = (𝟙 A) ^ c)
    (h₂ : ψ' ≫ χ' = (𝟙 A') ^ c) (h₃ : χ' ≫ ψ' = (𝟙 B') ^ c) (sq : φ ≫ ψ.left = ψ'.left ≫ φ') :
    φ' ≫ χ.left = χ'.left ≫ φ := by
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S' B' hB c hc
  haveI : Epi ((𝟙 B') ^ c).left := Flat.epi_of_flat_of_surjective _
  haveI : Epi (χ'.left ≫ ψ'.left) := by rw [← Over.comp_left, h₃]; infer_instance
  haveI : Epi ψ'.left := epi_of_epi χ'.left ψ'.left
  rw [← cancel_epi ψ'.left, ← Category.assoc, ← sq, Category.assoc, ← Over.comp_left, h₁, ← pow_left_comm h,
    ← h₂, Over.comp_left, Category.assoc]

open GlobalTheory.BirigidPow GlobalTheory.CechPic in

theorem val_adj {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) {T : Over S} (x : T ⟶ o'.A) (y : T ⟶ o.A) :
    BirigidPow.val o'.isLB x (y ≫ ψ) = BirigidPow.val o.isLB (x ≫ ψ') y := by
  have hc := hψ.pos
  obtain ⟨-, hm, -, -, ⟨hP⟩, -⟩ := hψ
  have nat : ∀ {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (G2 A).left} (hP : P.IsLB) {U V : Over S} (r : U ⟶ V)
      (x y : V ⟶ A), pull r.left (BirigidPow.val hP x y) = BirigidPow.val hP (r ≫ x) (r ≫ y) := by
    intro A _ _ P hP U V r x y
    rw [BirigidPow.val, BirigidPow.val, ← pull_comp, ← Over.comp_left, comp_lift]
  have hsq : ∀ {U : Over S} (x y : U ⟶ o.A), BirigidPow.val o'.isLB (x ≫ ψ) (y ≫ ψ) = c • BirigidPow.val o.isLB x y := by
    intro U x y
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    have e := (cls_eq_iff hL (pull_isLB o'.isLB _)).2 hP
    rw [BirigidPow.cls_lbPow o.isLB, cls_pull o'.isLB _ (pull_isLB o'.isLB _)] at e
    have e' := congrArg (pull (lift x y).left) e
    rw [map_nsmul] at e'
    refine Eq.trans ?_ e'.symm
    have := nat o'.isLB (lift x y) (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
    rw [lift_fst_assoc, lift_snd_assoc] at this
    exact this.symm
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c hc
  have H : BirigidPow.val o'.isLB (snd o.A o'.A) (fst o.A o'.A ≫ ψ) - BirigidPow.val o.isLB (snd o.A o'.A ≫ ψ') (fst o.A o'.A) = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc _ ?_ ?_
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, MonObj.one_comp, val_one_right _ o'.rig₂,
        val_one_right _ o.rig₂, sub_zero]
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]
      conv_lhs => rw [← h₂, ← Category.assoc, hsq]
      rw [← val_pow_left o.isLB o.ab o.ample o.rig₁ o.rig₂, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp]
  have := congrArg (pull (lift y x).left) H
  rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, map_zero, sub_eq_zero] at this
  exact this

open GlobalTheory.BirigidPow GlobalTheory.CechPic in

theorem dual_clauses {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₁ : ψ ≫ ψ' = (𝟙 o.A) ^ c) (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) :
    (∀ a : D.O, o'.act.act a ≫ ψ' = ψ' ≫ o.act.act a) ∧ (∀ x, o.eta (c • x) = o'.eta x ≫ ψ') ∧
      Nonempty (LBIso (Hecke.lbPow o'.P c) (o.P.pull (sq2 ψ'))) := by
  have hc := hψ.pos
  refine ⟨fun a => ?_, fun x => ?_, ⟨?_⟩⟩
  · haveI := GlobalTheory.UPel.HT.MulEpi.epi_pow_of_isAbelianScheme S o'.A o'.ab c hc
    haveI : Epi (ψ' ≫ ψ) := by rw [h₂]; infer_instance
    haveI : Epi ψ := epi_of_epi ψ' ψ
    haveI := o.act.hom a
    rw [← cancel_epi ψ, ← Category.assoc, ← hψ.2.2.1, Category.assoc, h₁, ← Category.assoc, h₁, MonObj.comp_pow,
      MonObj.pow_comp, Category.comp_id, Category.id_comp]
  · rw [hψ.2.2.2.1, Category.assoc, h₁, MonObj.comp_pow, Category.comp_id, eta_nsmul]
  · have hL : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
    refine (cls_eq_iff hL (pull_isLB o.isLB _)).1 ?_
    rw [BirigidPow.cls_lbPow o'.isLB, cls_pull o.isLB _ (pull_isLB o.isLB _)]
    change _ = BirigidPow.val o.isLB (fst o'.A o'.A ≫ ψ') (snd o'.A o'.A ≫ ψ')
    rw [← val_adj hψ h₂, Category.assoc, h₂, MonObj.comp_pow, Category.comp_id,
      val_pow_right o'.isLB o'.ab o'.ample o'.rig₁ o'.rig₂, BirigidPow.val, lift_fst_snd, Over.id_left, pull_id]

end GlobalTheory.UPel.HT.ESDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CrysProj

theorem hdR_projective : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  intro F _ _ k _ A₀ _ _ hA a
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · haveI : Fact (ringChar k).Prime := ⟨hp⟩
    refine GlobalTheory.T.de_rham_cohomology_projective_module F k ?_ A₀ hA a
    intro B₀ _ _ hB b
    set K := AlgebraicClosure k
    haveI : CharP K (ringChar k) := charP_of_injective_algebraMap (algebraMap k K).injective _
    obtain ⟨Λ, _, π, hπ, hker, hp2, hann⟩ := GlobalTheory.T.exists_flat_lift_mod_p_sq_perfect_field (ringChar k) K
    have hI : RingHom.ker π ^ 2 = 0 := by
      rw [hker, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.2 rfl]; rfl
    obtain ⟨hfin, hfree, f, hf, hk⟩ := GlobalTheory.T.crystal_finite_free_reduces_to_deRham F Λ K π hπ hI B₀ hB b
    letI := tensorModule (divided₂ hI) (spMap π) b
    haveI := isScalarTower_tensorModule (divided₂ hI) (spMap π) b
    letI := tensorModule (dp0 K) (𝟙 _) b
    exact GlobalTheory.T.projective_of_surjective_ker_le_smul (ringChar k) F Λ K π hπ hker hp2 hann _ hfin hfree _ f hf hk
  · haveI : CharP k 0 := hp ▸ ringChar.charP k
    haveI : CharZero k := CharP.charP_to_charZero k
    letI := tensorModule (dp0 k) (𝟙 _) a
    exact GlobalTheory.T.projective_charZero_tensor_ringOfIntegers' F k _

end GlobalTheory.CrysProj
end

