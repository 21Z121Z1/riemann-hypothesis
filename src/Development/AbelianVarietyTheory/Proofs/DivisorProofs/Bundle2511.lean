import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrpStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp : ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.TransAff.isAffineOpen_translates | exact GlobalTheory.TransAff.isAffineOpen_translates | (intros; apply GlobalTheory.TransAff.isAffineOpen_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfLbPowLbIsoLinComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePowLinComb

open GlobalTheory.CechPic

def genClasses (X : Scheme.{0}) : AddSubmonoid (Pic X) where
  carrier := {c | ∃ (A : LB X) (hA : A.IsLB), IsGenerated A ∧ cls A hA = c}
  zero_mem' := ⟨_, LB.isLB_triv X, isGenerated_triv X, rfl⟩
  add_mem' := by
    rintro _ _ ⟨A, hA, gA, rfl⟩ ⟨B, hB, gB, rfl⟩
    exact ⟨tens A B, isLB_tens hA hB, AmpleModelPos.isGenerated_tens gA gB, cls_tens hA hB _⟩

theorem isAmpleLB_of_lbPow_lbIso_linComb : ∀ (X : Scheme.{0}) (L M : LB X), IsAmpleLB M → L.IsLB →
    ∀ (N a₀ r : ℕ) (a : Fin r → ℕ) (β : Fin r → (X ⟶ X)), 1 ≤ N → 1 ≤ a₀ →
    LBIso (lbPow L N) (LB.LinComb M (K := Option (Fin r)) (fun o => o.elim (𝟙 X) fun i => β i)
      fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) → IsAmpleLB L := by
  intro X L M hM hL N a₀ r a β hN ha₀ H
  obtain ⟨k, hk, gk⟩ := hM.exists_isGenerated_pow
  have hMk := isLB_lbPow hM.isLB k

  set c : Pic X := ∑ i, a i • pull (β i) (cls _ hMk) with hc
  have hcmem : c ∈ genClasses X := by
    refine AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.nsmul_mem _ ?_ _
    exact ⟨_, pull_isLB hMk (β i), gk.pull (β i), cls_pull hMk (β i) _⟩
  obtain ⟨A, hA, gA, hAc⟩ := hcmem
  have hLN := isLB_lbPow hL (N * k)
  have hMa := isLB_lbPow hM.isLB (a₀ * k)
  have hAmp : IsAmpleLB (lbPow M (a₀ * k)) :=
    (isAmpleLB_pow_iff hM.isLB (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2 hM
  have h₁ := LB.isLB_div hLN hMa
  have h₂ := LB.isLB_div h₁ hA
  have hLpow : IsAmpleLB (lbPow L (N * k)) := hAmp.tensor_isGenerated gA hLN ((cls_eq_zero_iff h₂).1 ?_)
  · exact (isAmpleLB_pow_iff hL (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).1 hLpow
  have hE := (cls_eq_iff (isLB_lbPow hL N) (LB.isLB_linComb hM.isLB _ _)).2 H
  rw [cls_lbPow hL, cls_linComb hM.isLB, Fintype.sum_option] at hE
  rw [cls_div h₁ hA, cls_div hLN hMa, hAc, hc, cls_lbPow hL, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  simp only [Option.elim, pull_id] at hE
  simp only [map_nsmul]
  have e1 : (N * k) • cls L hL = k • (N • cls L hL) := by rw [smul_smul, mul_comm]
  rw [e1, hE]
  simp only [natCast_zsmul, smul_add, Finset.smul_sum, smul_smul]
  rw [sub_sub, sub_eq_zero, mul_comm a₀ k]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

end GlobalTheory.AmplePowLinComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGeneratedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_lbPow_mono_of_generated : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  first | exact @GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le | exact GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le | (intros; apply GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

variable {K : Type} [Field K]

abbrev baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B] : K →+* B :=
  (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))

def transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) : Sp (DualNumber B) ⟶ A.left :=
  if h : ∃ w, IsTransl φ x v w then h.choose else spMap (algebraMap B (DualNumber B)) ≫ x

theorem isTransl_transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) : IsTransl φ x v (transl φ x v) := by
  have h : ∃ w, IsTransl φ x v w := exists_isTransl φ x hx v
  rw [transl, dif_pos h]
  exact h.choose_spec

def dlogAt {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ) : B :=
  (valR (transl φ x v) Wo g.val).snd * valR x Wo g⁻¹.val

def chartVal {A : Over (Sp K)} [GrpObj A] {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (f : Γ(Z, Ω)) : B :=
  valR (x ≫ m) Ω f + algebraMap (DualNumber K) B DualNumber.eps *
    (valR (x ≫ m) Ω (δ f) + ∑ a, (∑ b, baseMap K B (θ a b) * dlogAt (baseMap K B) x (u b) Wo g) *
      (valR (transl (baseMap K B) x (u a) ≫ m) Ω f).snd)

def IsChartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) {Z : Scheme.{0}} (m : A.left ⟶ Z)
    (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (l : Sp B ⟶ A'.left) : Prop :=
  l ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧ ⊤ ≤ (l ≫ m') ⁻¹ᵁ Ω ∧
    ∀ f, valR (l ≫ m') Ω f = chartVal m Ω δ u θ Wo g x f

def chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) {Z : Scheme.{0}}
    (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) : Sp B ⟶ A'.left :=
  if h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l then h.choose else x ≫ i

theorem isChartPt_chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left)
    {Z : Scheme.{0}} (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ}
    (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
    (h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l) :
    IsChartPt A' m m' Ω δ u θ Wo g x (chartPt A' i m m' Ω δ u θ Wo g x) := by
  rw [chartPt, dif_pos h]
  exact h.choose_spec

theorem valR_eq_ev {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (f : Γ(Z, U)) : valR z U f = ev z U h f := by
  rw [valR, dif_pos h]
  rfl

theorem IsChartPt.unique {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z}
    (hm' : IsPullback m' A'.hom h y1) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ}
    {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ}
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l l' : Sp B ⟶ A'.left}
    (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l) (hl' : IsChartPt A' m m' Ω.1 δ u θ Wo g x l') : l = l' := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h1', h2', h3'⟩ := hl'
  have e : ev (l ≫ m') Ω.1 h2 = ev (l' ≫ m') Ω.1 h2' := by
    ext f
    rw [← valR_eq_ev, ← valR_eq_ev, h3 f, h3' f]
  have e2 : l ≫ m' = l' ≫ m' := by
    rw [← GlobalTheory.FlagMod.spMap_ev (l ≫ m') Ω.2 h2, ← GlobalTheory.FlagMod.spMap_ev (l' ≫ m') Ω.2 h2', e]
  exact hm'.hom_ext e2 (h1.trans h1'.symm)

end GlobalTheory.CechKS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem isClosedImmersion_kerι : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  intro R _ A T V _ φ H h hh
  have hP : IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom T.hom
  have w : pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) ≫ T.hom := by
    rw [Category.assoc]; exact pullback.condition
  let g : pullback A.hom (φ ≫ T.hom) ⟶ (A ⊗ T).left :=
    hP.lift (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) w
  have hg1 : g ≫ (fst A T).left = pullback.fst A.hom (φ ≫ T.hom) := hP.lift_fst _ _ _
  have hg2 : g ≫ (snd A T).left = pullback.snd A.hom (φ ≫ T.hom) ≫ φ := hP.lift_snd _ _ _
  have ht : IsPullback g (pullback.snd A.hom (φ ≫ T.hom)) (snd A T).left φ := by
    refine IsPullback.of_right (h₁₂ := (fst A T).left) (h₂₂ := T.hom) ?_ hg2 hP
    rw [hg1]
    exact IsPullback.of_hasPullback A.hom (φ ≫ T.hom)
  have hs : IsPullback (pullback.fst (h ≫ snd A T).left φ)
      ((kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)) (h.left ≫ (snd A T).left) φ := by
    have e1 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom) = pullback.snd (h ≫ snd A T).left φ :=
      pullback.lift_snd _ _ _
    rw [e1, ← Over.comp_left]
    exact IsPullback.of_hasPullback _ _
  have hsq : pullback.fst (h ≫ snd A T).left φ ≫ h.left = (kerι A φ h).left ≫ g := by
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, hg1]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, hg2, ← Over.comp_left, pullback.condition]
      exact congrArg (· ≫ φ) (pullback.lift_snd _ _ _).symm
  have hpb : IsPullback (pullback.fst (h ≫ snd A T).left φ) (kerι A φ h).left h.left g :=
    IsPullback.of_bot hs hsq ht
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb hh

end GlobalTheory.TwistFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocCocOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

abbrev SmallCat (W : K → X.left.Opens) : Type 1 := (IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).FullSubcategory

abbrev smallAt (W : K → X.left.Opens) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (h : Sm W x) :
    SmallCat W := ⟨trivAt x, h⟩

theorem Sm.map {W : K → X.left.Opens} {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') {x : Pt X D} (h : Sm W x) : Sm W (spOver φ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (trivMap φ x).le_preimage hi⟩

open Classical in

def cocOf (W : K → X.left.Opens) (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _))) :
    Fn1 X := fun _ _ _ _ _ _ φ x ↦
  if h : Sm W x then n (smallAt W x h) (smallAt W _ (h.map φ)) (ObjectProperty.homMk (trivMap φ x)) else 0

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt
variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

theorem isCoc_cocOf (W : K → X.left.Opens)
    (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)))
    (hn : ∀ (T T' T'' : SmallCat W) (a : T ⟶ T') (b : T' ⟶ T''), T.obj.J = ⊥ → T'.obj.J = ⊥ →
      T''.obj.J = ⊥ → d1 _ n T T' T'' a b = 0) : IsCoc W (cocOf W n) := by
  intro D _ _ D' _ _ D'' _ _ φ ψ x hx
  have tr : ∀ (y y' : Pt X D'') (e : y = y') (h : Sm W y) (h' : Sm W y')
      (f : smallAt W x hx ⟶ smallAt W y h) (f' : smallAt W x hx ⟶ smallAt W y' h'),
      (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f' := by
    rintro y _ rfl h h' f f' hf
    have : f = f' := ObjectProperty.hom_ext _ (Thick.hom_ext hf)
    subst this; rfl
  have key := hn (smallAt W x hx) (smallAt W _ (hx.map φ)) (smallAt W _ ((hx.map φ).map ψ))
    (ObjectProperty.homMk (trivMap φ x)) (ObjectProperty.homMk (trivMap ψ _)) rfl rfl rfl
  rw [d1_apply] at key
  simp only [cocOf, dif_pos hx, dif_pos (hx.map φ), dif_pos (hx.map (ψ.comp φ))]
  have e := tr (spOver (ψ.comp φ) ≫ x) (spOver ψ ≫ spOver φ ≫ x)
    (by rw [← spOver_comp, Category.assoc]) (hx.map (ψ.comp φ)) ((hx.map φ).map ψ)
    (ObjectProperty.homMk (trivMap (ψ.comp φ) x))
    ((ObjectProperty.homMk (trivMap φ x) : smallAt W x hx ⟶ smallAt W _ (hx.map φ)) ≫
      (ObjectProperty.homMk (trivMap ψ (spOver φ ≫ x)) : smallAt W _ (hx.map φ) ⟶ smallAt W _ ((hx.map φ).map ψ)))
    (fun _ ↦ rfl)
  rw [e]
  change ψ _ - _ + _ = 0 at key
  linear_combination -key
end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotentsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  first | exact @GlobalTheory.specQuotIdemCoprod | exact GlobalTheory.specQuotIdemCoprod | (intros; apply GlobalTheory.specQuotIdemCoprod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtGBaseChangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCombAtG_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Fin g → R) (σ : 𝓞 E →+* R) (u : Sp (DualNumber R) ⟶ t.G.left),
    (IsCombAtG t x e U u → IsCombAtG t (spMap φ ≫ x) (bcV t φ e) (fun b => φ (U b)) (spMap (dualMap φ) ≫ u)) ∧
    (IsEigG t σ u → IsEigG t (φ.comp σ) (spMap (dualMap φ) ≫ u)) := by
  first | exact @GlobalTheory.FlatModel.BaseChangeComb.bc_comb_eig | exact GlobalTheory.FlatModel.BaseChangeComb.bc_comb_eig | (intros; apply GlobalTheory.FlatModel.BaseChangeComb.bc_comb_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdealStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  first | exact @GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | exact GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | (intros; apply GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnectingSumMultDiag
section
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  [IsCocomm R A] [IsCocomm R B]

variable (R A) in

abbrev multDiag (i : ℕ) : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (mulBy R A i : A →ₐ[R] A) (AlgHom.id R _) (fun _ _ ↦ Commute.all _ _)

variable (R A) in

abbrev valZero : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (counitAlgHom R A) (counitAlgHom R A) (fun _ _ ↦ Commute.all _ _)

theorem map_multDiag (f : A →ₐc[R] B) (i : ℕ) (c : A ⊗[R] A) :
    f (multDiag R A i c) = multDiag R B i (pullbackTwo f c) := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp [map_mulBy]

omit [IsCocomm R A] [IsCocomm R B] in

theorem valZero_pullTwo (f : A →ₐc[R] B) (c : A ⊗[R] A) :
    valZero R B (pullbackTwo f c) = valZero R A c := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp

theorem counit_multDiag (i : ℕ) (c : A ⊗[R] A) :
    counit (R := R) (multDiag R A i c) = valZero R A c := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp

theorem pullTwo_mulBy_eq (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) (k : ℕ) :
    pullbackTwo (mulBy R A k) c = algebraMap R _ (valZero R A c) + k • c +
      cobOne R A (∑ i ∈ Finset.range k, multDiag R A i c) := by
  induction k with
  | zero =>
    have h0 : ∀ a : A, mulBy R A 0 a = algebraMap R A (counit a) := fun _ => rfl
    rw [Finset.sum_range_zero, map_zero, zero_smul, add_zero, add_zero]
    generalize c = t
    induction t with
    | zero => simp
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul a b =>
      simp [h0, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
        smul_smul, mul_comm]
  | succ k ih =>
    have h := pullTwo_convMul (mulBy R A k) (BialgHom.id R A) c hc
    have e : (toConv (mulBy R A k) * toConv (BialgHom.id R A)).ofConv = mulBy R A (k + 1) := by
      rw [mulBy, mulBy, pow_succ]
    have e2 : ∀ t : A ⊗[R] A, LinearMap.mul' R A (TensorProduct.map (mulBy R A k : A →ₗ[R] A)
        (BialgHom.id R A : A →ₗ[R] A) t) = multDiag R A k t := fun t => by
      induction t with
      | zero => simp
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul a b => simp
    rw [e, e2, pullTwo_id, ih] at h
    rw [h, Finset.sum_range_succ, map_add, succ_nsmul]
    abel

end PDiv

namespace PDivGroup

open PDiv

theorem isConnecting_sum_multDiag (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hp : (p : R) = 0)
    (G : PDivGroup p R) (z : G.cocycles) :
    G.IsConnecting (Submodule.Quotient.mk z) (∑ i ∈ Finset.range p,
      Algebra.TensorProduct.lift (mulBy R (G.A 1) i : G.A 1 →ₐ[R] G.A 1) (AlgHom.id R _)
        (fun _ _ ↦ Commute.all _ _) (z.1 1)) := by
  let B : G.funs := ⟨fun n => ∑ i ∈ Finset.range p, multDiag R (G.A n) i (z.1 n), fun n => by
    simp only [map_sum, map_multDiag, (z.2 n).2]⟩
  let K : G.funs := ⟨fun n => algebraMap R _ (valZero R _ (z.1 n)), fun n => by
    dsimp only
    rw [AlgHomClass.commutes, ← (z.2 n).2, valZero_pullTwo]⟩
  have hK : funsMap ((p : ℤ_[p]) • 𝟙 G) K = K :=
    Subtype.ext (funext fun n => AlgHomClass.commutes (Hom.app _ n) _)
  refine ⟨z + G.cob K, B, (Submodule.Quotient.eq _).2 ⟨K, by simp⟩, ?_, ?_, rfl⟩
  · rw [map_add, cocyclesMap_cob, hK]
    refine Subtype.ext (funext fun n => ?_)
    change cobOne R _ (B.1 n) = pullbackTwo (((p : ℤ_[p]) • 𝟙 G : G ⟶ G).app n) (z.1 n) +
      cobOne R _ (algebraMap R _ (valZero R _ (z.1 n)))
    rw [natCast_smul_id_app, pullTwo_mulBy_eq _ (z.2 n).1, ← Nat.cast_smul_eq_nsmul R, hp,
      zero_smul, add_zero, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      map_smul, cobOne_apply 1, comul_one, Algebra.TensorProduct.one_def, sub_self, zero_sub,
      smul_neg]
    abel
  · simp only [map_sum, counit_multDiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp,
      zero_mul]

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' : Type) [CommRing B'] [Algebra R B'] (a b c : B →ₐ[R] B') (θ θ' : Ω[B₀⁄R₀] →+ B'), IsTheta I p a b θ → (IsTheta I p b a (-θ) ∧ (IsTheta I p b c θ' → IsTheta I p a c (θ + θ')) ∧ (IsTheta I p a b θ' → θ = θ') ∧ (θ = 0 → a = b)) := by
  first | exact @GlobalTheory.Obs.isTheta_add | exact GlobalTheory.Obs.isTheta_add | (intros; apply GlobalTheory.Obs.isTheta_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDifferenceDerivationOfLifts_comp : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (E E' : Type) [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E'] (a b : B →ₐ[R] E) (θ : Ω[B₀⁄R₀] →+ E), IsTheta I p a b θ → (∀ g : E →ₐ[R] E', IsTheta I p (g.comp a) (g.comp b) ((g : E →+* E').toAddMonoidHom.comp θ)) ∧ ∀ (h : B' →ₐ[R] B) (h₀ : B₀' →ₐ[R₀] B₀), (∀ x, p (h x) = h₀ (p' x)) → IsTheta I p' (a.comp h) (b.comp h) (θ.comp (SemiHom.of_algHom h₀).m1.toAddMonoidHom) := by
  first | exact @GlobalTheory.Obs.isTheta_comp | exact GlobalTheory.Obs.isTheta_comp | (intros; apply GlobalTheory.Obs.isTheta_comp <;> assumption)
end

