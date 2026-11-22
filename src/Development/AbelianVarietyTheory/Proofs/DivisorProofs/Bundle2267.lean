import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedDataTransportIdentityLevelChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem descData_transport_id : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  intro h n N d B B' _ _ ζ ζ' X Y s s' C c π A₀ _ φ φ₂ P₀ lev₀ hS hA hsq hP₀ hw hlev
  obtain ⟨ψ, hψ, ⟨ψ₂, hsqψ, hC⟩, hlevψ⟩ := hS
  haveI : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  obtain ⟨e, he, heψ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl c.A)) hψ
  haveI := he
  have heψ' : e.hom.left ≫ ψ = 𝟙 _ := by simpa using heψ
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hψe : ψ = e.inv.left := by
    rw [← Category.id_comp ψ, ← hie, Category.assoc, heψ', Category.comp_id]
  let E₂ : G2 c.A ⟶ G2 C.A := lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)
  have hE₂ : E₂.left ≫ ψ₂ = 𝟙 _ := by
    have := GlobalTheory.SiegelDescent.lift_square hsqψ (τ := 𝟙 (G2 c.A).left) (a := fst c.A c.A ≫ e.hom)
      (b := snd c.A c.A ≫ e.hom) (a₀ := fst c.A c.A) (b₀ := snd c.A c.A)
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
    rw [this, lift_fst_snd, Over.id_left, Category.comp_id]
  refine ⟨e.hom.left ≫ φ, E₂.left ≫ φ₂, ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp π) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h1 : LBIso (C.P.pull E₂.left) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame P₀ _ (fun _ => φ₂) _ E₂.left fun _ => rfl) hw
    have h2 : LBIso (C.P.pull E₂.left) (c.P.pull (E₂.left ≫ ψ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame c.P _ (fun _ => ψ₂) _ E₂.left fun _ => rfl) hC
    have h3 : LBIso (c.P.pull (E₂.left ≫ ψ₂)) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.trans (pull_isLB c.isLB _) (pull_isLB C.isLB _) (pull_isLB hP₀ _) h2.symm h1
    exact LBIso.chartPull (chartPullUnpull c.P _ hE₂)
      (chartPullSame P₀ _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h3
  · intro a
    have h₀ := hlevψ a
    rw [pow_one, Category.id_comp, hψe] at h₀
    rw [← h₀, Category.assoc, ← Category.assoc e.inv.left, hie, Category.id_comp, hlev a]

end GlobalTheory.SiegLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionZeroCase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.DimZero

section Basics

variable {R : Type} [CommRing R] [IsDomain R]

theorem isIso_hom (D : DegPre R) (hg : D.P.g = 0) : IsIso D.P.A.hom :=
  GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)

theorem hom_subsingleton (D : DegPre R) (hg : D.P.g = 0) (T : Over (Sp R)) : Subsingleton (T ⟶ D.P.A) := by
  haveI := isIso_hom D hg
  refine ⟨fun f f' => Over.OverMorphism.ext ?_⟩
  rw [← cancel_mono D.P.A.hom, Over.w f, Over.w f']

theorem subsingleton_A {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : Subsingleton N.A := by
  haveI := hom_subsingleton D hg (TF (R := R) F)
  exact ⟨fun x y => ν.eA.injective (Subsingleton.elim _ _)⟩

theorem th_one_ne_zero {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : N.th 1 ≠ 0 := by
  haveI : IsIso D.P.A.hom := isIso_hom D hg
  have he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  have he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _ := by
    rw [← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]
    exact (congrArg _ he).trans (Category.comp_id _)
  obtain ⟨s, hs⟩ := GlobalTheory.MBLow.AbKey.exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he'
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom)
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)
  obtain ⟨r, hr⟩ := ν.th_gen s
  have hu : ∀ j, IsUnit (ν.th.f j) := fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)
  intro h0
  have h := ν.th_eq 1
  rw [h0, zero_mul] at h
  have hU : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ D.P.L.U (ν.J (ν.eA 1).left) := ν.good _
  have hx : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left)
      (fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _)) := fun y hy => Set.mem_iInter.2 fun _ => by
    rw [Category.comp_id]; exact hU hy
  unfold sF valF at h
  rw [dif_pos hx] at h
  exact (((hu _).map _).map _).ne_zero h.symm

end Basics

section Classical

variable {g : ℕ}

theorem dot_empty [IsEmpty (Fin g)] (u v : Fin g → ℂ) : u ⬝ᵥ v = 0 := by
  simp [dotProduct]

theorem thetaChar_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b z : Fin g → ℂ) :
    thetaChar τ a b z = 1 := by
  unfold thetaChar
  rw [tsum_fintype, Fintype.sum_unique]
  simp [dot_empty]

theorem autV_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b M N z = 1 := by
  simp [autV, dot_empty]

theorem posDef_empty [IsEmpty (Fin g)] (A : Matrix (Fin g) (Fin g) ℝ) : A.PosDef :=
  ⟨by ext i; exact isEmptyElim i, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩

theorem differentiableOn_empty [IsEmpty (Fin g)] (f : (Fin g → ℂ) → ℂ) (s : Set (Fin g → ℂ)) :
    DifferentiableOn ℂ f s := fun x _ =>
  ((hasFDerivAt_const (f x) x).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => congrArg f (Subsingleton.elim y x))).differentiableAt.differentiableWithinAt

def abZero (B : NumB ℂ) (g : ℕ) (hg : g = 0) (hA : Subsingleton B.A) (hth : B.th 1 ≠ 0) : AB B g where
  τ := 0
  a := 0
  b := 0
  c := B.th 1
  symm := by ext i; haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  pos := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact posDef_empty _
  ha i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hb i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hc := hth
  ex _ := 1
  ex_add _ _ := (mul_one 1).symm
  onto x := ⟨0, Subsingleton.elim _ _⟩
  ker z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    exact ⟨fun _ => ⟨0, 0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  fr _ := 1
  fr_zero := rfl
  fr_per M N z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [autV_empty]
  th z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [thetaChar_empty]

end Classical

section Geo

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem valF_eq_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := rfl

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) : (res e u).val = resG X e u.val := rfl

def frZ (ν : NumOf D ℂ N) (i : D.P.L.ι) : ℂ :=
  valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U (ν.J (ν.eA 1).left)) (D.P.L.g i (ν.J (ν.eA 1).left)).val * ν.rg

theorem frZ_compat (ν : NumOf D ℂ N) (i j : D.P.L.ι) (h : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j)) :
    frZ ν i = valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U j) (D.P.L.g i j).val * frZ ν j := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have h3 : ⊤ ≤ x ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j ⊓ D.P.L.U k) := fun y hy => ⟨h hy, hk hy⟩
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.cocycle i j k)
  simp only [Units.val_mul] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x _ h3, val_res, val_res, val_res, GlobalTheory.ZH.CrdCalc.valR_res x _ h3,
    GlobalTheory.ZH.CrdCalc.valR_res x _ h3, GlobalTheory.ZH.CrdCalc.valR_res x _ h3] at c
  simp only [valF_eq_valR]
  rw [← c]
  ring

theorem frZ_self (ν : NumOf D ℂ N) : frZ ν (ν.J (ν.eA 1).left) = ν.rg := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.g_self k)
  simp only [val_res, Units.val_one] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_res x _ hk, GlobalTheory.ZH.CrdCalc.valR_eq x _ hk, map_one] at c
  rw [valF_eq_valR, c, _root_.one_mul]

theorem isD_zero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (b : TE R ℂ ⟶ D.P.A) : IsD ν d 0 b := by
  haveI := hom_subsingleton D hg (TE R ℂ)
  intro U f hU
  have hb : b = (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0) :=
    Subsingleton.elim _ _
  have hl : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    rw [hb]
    have e : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        ((Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id]
    rw [e]
    rfl
  rw [hl, (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ U hU).2, map_zero, TrivSqZeroExt.inr_zero, add_zero,
    TrivSqZeroExt.algebraMap_eq_inl]
  rfl

def geoZero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (hg' : g = 0) (hex : ∀ z, d.ex z = 1)
    (hfr : ∀ z, d.fr z = 1) : Geo ν d where
  frG i _ := frZ ν i
  hol U f := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact ⟨isOpen_discrete _, differentiableOn_empty _ _⟩
  fr_hol i := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact differentiableOn_empty _ _
  fr_compat i j z h := by
    rw [hex] at h ⊢
    exact frZ_compat ν i j h
  fr_eq z := by
    rw [hex, hfr, Units.val_one, _root_.one_mul]
    exact (frZ_self ν).symm
  dif b _ := ⟨0, isD_zero ν hg d b⟩

end Geo

section Main

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

theorem keyOK_zero (κ : Rule) (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB D.P.g) (hc : d.c = N.th 1) :
    KeyOK κ ν d := by
  intro vB b MB k₀ _ _ _ hk
  haveI : IsEmpty (Fin D.P.g) := hg ▸ inferInstance
  rw [Matrix.det_isEmpty, one_pow, hc, mul_comm]
  exact ⟨one_ne_zero, hk.1 hg⟩

theorem main : ∀ κ : Rule, AllC fun {R} _ _ {D} _ {N} ν => D.P.g = 0 →
    ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ R _ _ _ _ D _ _ _ N ν hg
  let d := abZero N.toNumB D.P.g hg (subsingleton_A ν hg) (th_one_ne_zero ν hg)
  exact ⟨d, geoZero ν hg d hg (fun _ => rfl) (fun _ => rfl), keyOK_zero κ ν hg d rfl⟩

end Main

end GlobalTheory.MBLow.DimZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointOverOriginLiftsTangentVectorUniformisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualPointOverOrigin_lifts_tangentVector_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left), IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ →
    eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A →
    ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left →
      ∃ b' : epsR ℂ ⟶ x.P.A, IsTangent b' ∧ b'.left ≫ φ = b.left := by
  first | exact @GlobalTheory.MBLow.Cl.tangent_lift_of_pullback | exact GlobalTheory.MBLow.Cl.tangent_lift_of_pullback | (intros; apply GlobalTheory.MBLow.Cl.tangent_lift_of_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O

def Setup.DualRef {D : D7} (O : Setup D) : Prop :=
  ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (x : DV.Rt D.what₂.Tau O.N) (z : Pts (O.var c) σ) (f : (O.var c).Fn),
    (divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under z) f →
      (cxSt _).pn _ σ _ (O.met.h0 c σ (O.ex x)) ((cxSt _).cx _ σ f) z *
        (cxSt _).pn _ σ _ (O.met.h0 c σ (-O.ex x)) ((cxSt _).cx _ σ f⁻¹) z = 1

end GlobalTheory.Mean4O
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdDetSubOneOfCongModThreeLe
section
open GlobalTheory.Poinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L N : ℕ) (hL : 3 ≤ L)
    (γ : X ≃ₗ[ℤ] X) (hγ : ∀ x, CongMod L (γ x) x) : (N : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
  set b := Module.Free.chooseBasis ℤ X
  have hdet : LinearMap.det (γ : X →ₗ[ℤ] X) = (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)).det :=
    (LinearMap.det_toMatrix b _).symm
  have hmap : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)) = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hγ (b j)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hw,
      map_add, map_nsmul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Matrix.one_apply]
    rw [Finsupp.single_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, add_zero]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcast : ((LinearMap.det (γ : X →ₗ[ℤ] X) : ℤ) : ZMod L) = 1 := by
    rw [hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod L)) (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X))
    simp only [eq_intCast] at this
    rw [this, hmap, Matrix.det_one]
  have hdvd : (L : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast, sub_self]
  rcases Int.isUnit_iff.mp (LinearEquiv.isUnit_det' γ) with h | h
  · rw [h, sub_self]; exact dvd_zero _
  · exfalso
    rw [h] at hdvd
    have h2 : (L : ℤ) ∣ 2 := by
      have : (2 : ℤ) = -(-1 - 1) := by norm_num
      rw [this]; exact (dvd_neg).2 hdvd
    have : L ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

theorem GlobalTheory.dvr_eq_localization_integralClosure : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) → ∀ s ∈ V, ∃ b d : L, (b ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ b = 0) ∧ (d ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ d = 0) ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro K L _ _ _ φ hfin V _ hE s hs
  letI : Algebra K L := φ.toAlgebra
  haveI : FiniteDimensional K L := hfin
  set E : ValuationSubring K := V.comap φ with hEdef
  letI : Algebra E L := (φ.comp E.subtype).toAlgebra
  haveI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsFractionRing E K := inferInstance
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure E L) := integralClosure.isDedekindDomain E K L
  haveI : IsFractionRing (integralClosure E L) L := integralClosure.isFractionRing_of_finite_extension K L

  have hBV : ∀ x : L, IsIntegral E x → x ∈ V := by
    intro x hx
    letI : Algebra E V := ((φ.comp E.subtype).codRestrict V (fun y => y.2)).toAlgebra
    haveI : IsScalarTower E V L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have h2 : IsIntegral V x := IsIntegral.tower_top hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    rw [← hy]; exact y.2

  have hpoly : ∀ x : L, IsIntegral E x →
      ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 := by
    rintro x ⟨p, hpm, hp⟩
    refine ⟨p.map E.subtype, hpm.map _, fun i => ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff i).2
    · rw [Polynomial.eval₂_map]; exact hp
  set B := integralClosure E L
  let f : B →+* V :=
    { toFun := fun b => ⟨(b : L), hBV _ b.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  haveI hnp : n.IsPrime := Ideal.comap_isPrime _ _

  have hn0 : n ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E
    have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    intro hbot
    have hmem : algebraMap E B ϖ ∈ n := by
      show f (algebraMap E B ϖ) ∈ IsLocalRing.maximalIdeal V
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hϖ.not_isUnit
      have h1 : ((u⁻¹ : Vˣ) : V) * f (algebraMap E B ϖ) = 1 := by rw [← hu]; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V) : L)) * φ ϖ = 1 := congrArg Subtype.val h1
      have h3 : (ϖ : K)⁻¹ ∈ E := by
        show φ ((ϖ : K)⁻¹) ∈ V
        rw [map_inv₀, inv_eq_of_mul_eq_one_left h2]; exact (((u⁻¹ : Vˣ) : V)).2
      exact isUnit_iff_exists_inv.2 ⟨⟨_, h3⟩, Subtype.ext (mul_inv_cancel₀ hϖ0)⟩
    rw [hbot, Ideal.mem_bot] at hmem
    have h4 : φ (ϖ : K) = 0 := congrArg (fun b : B => (b : L)) hmem
    exact hϖ0 ((map_eq_zero φ).1 h4)
  have hunit : ∀ d : B, d ∉ n → (d : L) ≠ 0 ∧ (d : L)⁻¹ ∈ V := by
    intro d hd
    have hu : IsUnit (f d) := by
      by_contra h
      exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu⟩ := hu
    have h1 : f d * ((u⁻¹ : Vˣ) : V) = 1 := by rw [← hu]; exact u.mul_inv
    have h2 : (d : L) * ((((u⁻¹ : Vˣ) : V) : L)) = 1 := congrArg Subtype.val h1
    refine ⟨left_ne_zero_of_mul_eq_one h2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h2]; exact (((u⁻¹ : Vˣ) : V)).2
  let O := Localization.AtPrime n
  letI : Algebra O L := IsLocalization.localizationAlgebraOfSubmonoidLe O L n.primeCompl
    (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsScalarTower B O L := IsLocalization.localization_isScalarTower_of_submonoid_le O L
    n.primeCompl (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsFractionRing O L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization n.primeCompl O L
  haveI : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hn0 O
  have hO : ∀ z : O, ∃ b d : B, d ∉ n ∧ algebraMap O L z * (d : L) = (b : L) := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective n.primeCompl z
    refine ⟨a, t, t.2, ?_⟩
    show algebraMap O L (IsLocalization.mk' O a t) * algebraMap B L t = algebraMap B L a
    rw [IsScalarTower.algebraMap_apply B O L (t : B), IsScalarTower.algebraMap_apply B O L a,
      ← map_mul, IsLocalization.mk'_spec]
  by_cases hs0 : s = 0
  · refine ⟨0, 1, ⟨hBV _ isIntegral_zero, hpoly _ isIntegral_zero⟩,
      ⟨hBV _ isIntegral_one, hpoly _ isIntegral_one⟩, one_ne_zero, by rw [inv_one]; exact V.one_mem, ?_⟩
    rw [hs0, zero_div]
  rcases ValuationRing.isInteger_or_isInteger O s with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    refine ⟨b, d, ⟨hBV _ b.2, hpoly _ b.2⟩, ⟨hBV _ d.2, hpoly _ d.2⟩, (hunit d hd).1,
      (hunit d hd).2, ?_⟩
    rw [← hz, ← hbd, mul_div_cancel_right₀ _ (hunit d hd).1]
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    rw [hz] at hbd
    have hsb : s * (b : L) = d := by rw [← hbd, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    have hb : b ∉ n := by
      intro hb
      have hb' : ¬ IsUnit (f b) := (IsLocalRing.mem_maximalIdeal _).1 hb
      have hfd : IsUnit (f d) := by
        by_contra h
        exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
      have hm : (⟨s, hs⟩ : V) * f b = f d := Subtype.ext hsb
      rw [← hm] at hfd
      exact hb' (isUnit_of_mul_isUnit_right hfd)
    refine ⟨d, b, ⟨hBV _ d.2, hpoly _ d.2⟩, ⟨hBV _ b.2, hpoly _ b.2⟩, (hunit b hb).1,
      (hunit b hb).2, ?_⟩
    rw [eq_div_iff (hunit b hb).1, hsb]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantNormalProjectiveCompactificationStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_normal_projective_compactification : ∀ (F : Type) [Field F] [NumberField F] (X V : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (j : V ⟶ X) [IsOpenImmersion j] (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut V), IsProjOver sX → Nonempty V → GlobalTheory.IsNormalScheme V → (∀ γ, (ρ γ).hom ≫ j ≫ sX = j ≫ sX) → ∃ (X' W : Scheme.{0}) (φ : X' ⟶ X) (ℓ : V ⟶ X') (ρ' : Γ →* Aut X') (q : X' ⟶ W) (sW : W ⟶ Sp F) (_ : IsIntegral X'), GlobalTheory.IsNormalScheme X' ∧ IsProjOver (φ ≫ sX) ∧ IsOpenImmersion ℓ ∧ ℓ ≫ φ = j ∧ (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) ∧ IsAffineQuotient ρ' q ∧ q ≫ sW = φ ≫ sX ∧ IsProjOver sW ∧ IsIntegral W ∧ IsFinite q ∧ Surjective q := by
  first | exact @GlobalTheory.EqModel.exists_equivariant_model | exact GlobalTheory.EqModel.exists_equivariant_model | (intros; apply GlobalTheory.EqModel.exists_equivariant_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfOneMeasureStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_at_of_one_measure : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D → ∀ i : Fin D.R.m, ExactAt p i := by
  first | exact @GlobalTheory.CovTop.MeasRd.exactAt_of_rows | exact GlobalTheory.CovTop.MeasRd.exactAt_of_rows | (intros; apply GlobalTheory.CovTop.MeasRd.exactAt_of_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomainStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_ratio_of_fundamental_domain : ∀ (hP : Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  first | exact @GlobalTheory.ExactRatioProof.exactRatio | exact GlobalTheory.ExactRatioProof.exactRatio | (intros; apply GlobalTheory.ExactRatioProof.exactRatio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparisonStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_of_comparison : CmpSt → ExSt := by
  first | exact @GlobalTheory.FlatModel.exSt_of_cmpSt | exact GlobalTheory.FlatModel.exSt_of_cmpSt | (intros; apply GlobalTheory.FlatModel.exSt_of_cmpSt <;> assumption)
end

