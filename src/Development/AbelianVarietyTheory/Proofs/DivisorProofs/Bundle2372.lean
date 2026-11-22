import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem restrict_cover_affine_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  intro R _ X s J U hU
  apply restrict_bijective_one_of_basis s
  · intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let G : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span G = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  · intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩

end GlobalTheory.CechDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTrivialPullbackOfIsPullbackGenerator
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

lemma res_res_pull {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem triv_pull_of_isPullGen : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → Triv (M.pull p) := by
  intro X Y p M e he
  refine ⟨⟨fun j => res (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit) (e (j PUnit.unit))⟩, fun i j => ?_⟩
  have gg : (M.pull p).g i j = res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
      (pullU p _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
    (Fintype.prod_unique (fun k : PUnit => (res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i k))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j k)))
      (pullU p _ (M.g (i k) (j k)))) ^ (1 : ℤ))).trans (zpow_one _)
  rw [gg]
  have h := he (i PUnit.unit) (j PUnit.unit) (LB.wchart M (fun _ : PUnit => p) i ⊓ LB.wchart M (fun _ : PUnit => p) j)
    (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
    (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit))
    (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
  refine (res_res_pull _ _ _).trans (h.trans ?_)
  exact congrArg _ (res_res_pull _ _ _).symm

end GlobalTheory.CharKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

abbrev Above (m : ℕ) : Type := {p : Fin m × Fin m // p.1 < p.2}

def IsLowInv (L : Matrix (Fin m) (Fin m) R) : Prop := (∀ i j, i < j → L i j = 0) ∧ ∀ i, IsUnit (L i i)

def upMat (a : Above m → R) : Matrix (Fin m) (Fin m) R := fun i j =>
  if h : i < j then a ⟨(i, j), h⟩ else if i = j then 1 else 0

def InCell (M : Matrix (Fin m) (Fin m) R) (w : Equiv.Perm (Fin m)) (a : Above m → R) : Prop :=
  ∃ L, IsLowInv L ∧ M.submatrix id w = L * upMat a

end Mat

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

abbrev Coord (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Above (Dw.mult τ)

def CellAt (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)))
    (U : C.Y.X.Opens) (a : ∀ τ : E →+* ℂ, Above (Dw.mult τ) → Γ(C.Y.X, U)) : Prop :=
  ∃ (hU : IsAffineOpen U) (hUV : U ≤ C.π ⁻¹ᵁ V) (hg : genericPoint C.Y.X ∈ U) (φ : c.F →+* Γ(C.Y.X, U))
    (fr : EigFrame Z φ ((hU.fromSpec ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
    (hx : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec ≫ genι Z = (hU.fromSpec ≫ C.π) ≫ genι Z)
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U)),
    (hU.fromSpec ≫ C.π) ≫ genStr Z = spMap φ ∧ fr.Tri (fnOf U hg) C.f0 t ∧
    (∀ τ i, fr.vec τ i = ∑ k, A τ i k • GlobalTheory.LieLocFrame.res (C.π.appLE V U hUV).hom hx (f₀.vec τ k)) ∧
    ∀ τ, InCell (A τ) (w τ) (a τ)

def cellOpen (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) : C.Y.X.Opens :=
  sSup {U | ∃ a, CellAt C hV f₀ w U a}

theorem cellOpen_le (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    cellOpen C hV f₀ w ≤ C.π ⁻¹ᵁ V :=
  sSup_le fun _ ⟨_, _, hUV, _⟩ => hUV

def cellMap (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    (cellOpen C hV f₀ w).toScheme ⟶ V.toScheme :=
  C.π.resLE V _ (cellOpen_le C hV f₀ w)

theorem cellMap_ι (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    cellMap C hV f₀ w ≫ V.ι = (cellOpen C hV f₀ w).ι ≫ C.π :=
  Scheme.Hom.resLE_comp_ι _ _

def IsCoord (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)))
    (u : Coord Dw → Γ(C.Y.X, cellOpen C hV f₀ w)) : Prop :=
  ∀ (U : C.Y.X.Opens) (a : ∀ τ : E →+* ℂ, Above (Dw.mult τ) → Γ(C.Y.X, U)), CellAt C hV f₀ w U a →
    ∀ (hle : U ≤ cellOpen C hV f₀ w) (τ : E →+* ℂ) (p : Above (Dw.mult τ)),
      C.Y.X.presheaf.map (homOfLE hle).op (u ⟨τ, p⟩) = a τ p

def coordTop (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)))
    (u : Coord Dw → Γ(C.Y.X, cellOpen C hV f₀ w)) (i : Coord Dw) : Γ((cellOpen C hV f₀ w).toScheme, ⊤) :=
  (cellOpen C hV f₀ w).topIso.inv (u i)

end Geo

end GlobalTheory.ShFam.Cell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centred_point_phi_positive : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  first | exact @GlobalTheory.DegVal.exists_phiAt_pos | exact GlobalTheory.DegVal.exists_phiAt_pos | (intros; apply GlobalTheory.DegVal.exists_phiAt_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false

namespace GlobalTheory.UPel.HT.ES.KerUPart

theorem exists_elt {O : Type} [CommRing O] (I J : Ideal O) (q : O) (h : IsCoprime I J)
    (hq : I * J ≤ Ideal.span {q}) (E : ℕ) :
    ∃ α : O, (∀ a ∈ I ^ E, ∃ u v, a = u * α + v * q ^ E) ∧ ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ v, α = a + v * q ^ E := by
  have hm : ∀ a ∈ I ^ E, ∀ b ∈ J ^ E, ∃ v, a * b = v * q ^ E := fun a ha b hb => by
    have h1 : a * b ∈ (I * J) ^ E := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    have h2 := Ideal.pow_right_mono hq E h1
    rw [Ideal.span_singleton_pow] at h2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨v, hv.symm⟩
  have hc : ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ b ∈ J ^ E, a + b = 1 := fun e =>
    Ideal.isCoprime_iff_exists.1 (h.pow (m := e) (n := E))
  obtain ⟨α, hα, β, hβ, hαβ⟩ := hc E
  refine ⟨α, fun a ha => ?_, fun e => ?_⟩
  · obtain ⟨v, hv⟩ := hm a ha β hβ
    exact ⟨a, v, by linear_combination hv - a * hαβ⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hc e
    obtain ⟨v, hv⟩ := hm α hα b hb
    exact ⟨α * a, Ideal.mul_mem_left _ _ ha, v, by linear_combination hv - α * hab⟩

theorem exists_conj {p : ℕ} [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤)
    (hu : uIdeal D r ≤ w) :
    ∃ J : Ideal (𝓞 D.F), IsCoprime (uIdeal D r) J ∧ uIdeal D r * J ≤ Ideal.span {(p : 𝓞 D.F)} := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hM : (D.ω - r) * (D.bar D.ω - r) = ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) := by
    push_cast
    linear_combination hnm - r * htr
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hn
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hn
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, ← hM, Int.cast_one, Int.cast_natCast] at h
    refine hw ((Ideal.eq_top_iff_one w).2 (h ▸ w.add_mem (w.mul_mem_left _ (hu (p_mem_uIdeal D r)))
      (w.mul_mem_left _ (w.mul_mem_right _ (hu (sub_mem_uIdeal D r))))))
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Int.cast_mul, Int.cast_natCast] at hM
  refine ⟨Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r}, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 D.disc_p
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    push_cast at h
    refine Ideal.isCoprime_iff_exists.2 ⟨x * p + y * (D.ω - D.bar D.ω) * (D.ω - r),
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ (p_mem_uIdeal D r)) (Ideal.mul_mem_left _ _ (sub_mem_uIdeal D r)),
      -(y * (D.ω - D.bar D.ω)) * (D.bar D.ω - r),
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
    linear_combination h + y * (D.ω + D.bar D.ω + D.tr) * htr - 4 * y * hnm
  · rw [uIdeal, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    rintro z (rfl | rfl | rfl | rfl)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
    · exact Ideal.mem_span_singleton.2 (hM ▸ dvd_mul_right _ _)

section Grp

variable {S : Scheme.{0}}

theorem comp_mulN {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) : x ≫ mulN A n = x ^ n := by
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem exists_zeroLocus {B Z : Over S} [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (g : Z ⟶ B) (hg : g ^ n = 1) :
    ∃ (Y : Over S) (j : Y ⟶ Z), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ Z), (∃ z, z ≫ j = y) ↔ y ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B hn
  have hsec := GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion B n).hom _
    (Over.w (GlobalTheory.HTTorsRep.torsEta (A := B) n))
  have := GlobalTheory.HTTorsRep.mono_of_unit (GlobalTheory.HTTorsRep.torsEta (A := B) n)
  have := GlobalTheory.HTTorsRep.mono_ι (A := B) n
  let g' : Z ⟶ torsion B n := pullback.lift g (toUnit Z) (by rw [comp_mulN, hg]; rfl)
  have hg' : g' ≫ torsion.ι B n = g := pullback.lift_fst _ _ _
  have hP := (IsPullback.of_hasPullback g' (GlobalTheory.HTTorsRep.torsEta n)).map (Over.forget S)
  refine ⟨pullback g' (GlobalTheory.HTTorsRep.torsEta n), pullback.fst _ _, inferInstance,
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2, fun W y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [← hg', Category.assoc, ← Category.assoc (pullback.fst g' _), pullback.condition, Category.assoc,
      GlobalTheory.HTTorsRep.torsEta_ι, ← Category.assoc, toUnit_unique (z ≫ pullback.snd g' _) (toUnit W)]
    rfl
  · refine ⟨pullback.lift y (toUnit W) ?_, pullback.lift_fst _ _ _⟩
    rw [← cancel_mono (torsion.ι B n), Category.assoc, hg', h, Category.assoc, GlobalTheory.HTTorsRep.torsEta_ι]
    rfl

theorem exists_subgroup {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C]
    [IsCommMonObj C] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hC : IsAbelianScheme C) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (f : A ⟶ B) (g : A ⟶ C) [IsMonHom f] [IsMonHom g] :
    ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧
      ∀ (T : Over S) (x : T ⟶ A), InSub i x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  have := GlobalTheory.HTTorsRep.mono_ι (A := A) n
  have h0 : torsion.ι A n ^ n = 1 := by rw [← comp_mulN, GlobalTheory.HTTorsRep.ι_mulN]; rfl
  obtain ⟨Y, j, hj, hjo, hjc, hY⟩ := exists_zeroLocus hB hn (torsion.ι A n ≫ f)
    (by rw [← MonObj.pow_comp, h0, MonObj.one_comp])
  obtain ⟨K, k, hk, hko, hkc, hK⟩ := exists_zeroLocus hC hn (j ≫ torsion.ι A n ≫ g)
    (by rw [← MonObj.comp_pow, ← MonObj.pow_comp, h0, MonObj.one_comp, MonObj.comp_one])
  have hpts : ∀ (T : Over S) (x : T ⟶ A),
      InSub (k ≫ j ≫ torsion.ι A n) x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
    intro T x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← MonObj.comp_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, h0]
        simp only [MonObj.comp_one]
      · simpa only [Category.assoc] using (hY T (z ≫ k ≫ j)).1 ⟨z ≫ k, Category.assoc _ _ _⟩
      · simpa only [Category.assoc] using (hK T (z ≫ k)).1 ⟨z, rfl⟩
    · rintro ⟨h1, h2, h3⟩
      let y : T ⟶ torsion A n := pullback.lift x (toUnit T) (by rw [comp_mulN, h1]; rfl)
      have hy : y ≫ torsion.ι A n = x := pullback.lift_fst _ _ _
      obtain ⟨z, hz⟩ := (hY T y).2 (by rw [← Category.assoc, hy, h2])
      obtain ⟨u, hu⟩ := (hK T z).2 (by rw [← Category.assoc, hz, ← Category.assoc, hy, h3])
      exact ⟨u, by rw [← Category.assoc, hu, ← Category.assoc, hz, hy]⟩
  have hm : Mono (k ≫ j ≫ torsion.ι A n) := inferInstance
  have hfin : IsFinite K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  have het : Etale K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  generalize k ≫ j ≫ torsion.ι A n = i at hpts hm
  obtain ⟨i1, i2, i3⟩ := (hpts K i).1 ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨G, hG⟩ := GlobalTheory.overScheme_grpObj_of_mono_factor S A K i hm
    (by
      have e : (i ⊗ₘ i) ≫ μ[A] = (fst K K ≫ i) * (snd K K ≫ i) := by
        rw [Hom.mul_def]; congr 1
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, i1]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i2]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i3]; simp)
    (by
      have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [e]
      exact (hpts _ _).2 ⟨one_pow _, MonObj.one_comp _, MonObj.one_comp _⟩)
    (by
      have e : i ≫ ι[A] = i⁻¹ := rfl
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [inv_pow, i1, inv_one]
      · rw [GrpObj.inv_comp, i2, inv_one]
      · rw [GrpObj.inv_comp, i3, inv_one])
  exact ⟨K, G, i, hG, hm, hfin, het, hpts⟩

end Grp

theorem charZero_of_isUnit {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : Γ(S, ⊤))) (k : Type) [Field k] (x : Sp k ⟶ S) :
    CharZero k := by
  have hpk : (p : k) ≠ 0 := by
    have := hp.map (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
    rw [map_natCast] at this
    exact this.ne_zero
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    by_cases h : ringChar k = p
    · exact hpk (h ▸ h0)
    · have := (b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)).map β
      rw [map_natCast, h0] at this
      exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

theorem exists_kerUPart : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∀ (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → IsTj r w j o o' ψ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) ∧ IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ b N _ _ hm r w j c hw hu _ _ S _ s hp o o' ψ hψ hT
  obtain ⟨⟨E, rfl⟩, hψh, hlin, -, -, ψ', hψ'h, hψψ', -⟩ := hψ
  obtain ⟨J, hJ, hJp⟩ := exists_conj D r w hw.ne_top hu
  obtain ⟨α, hα1, hα2⟩ := exists_elt _ _ _ hJ hJp E
  have hc : IsUnit ((p ^ E : ℕ) : Γ(S, ⊤)) := by rw [Nat.cast_pow]; exact hp.pow E
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : ∀ a, IsMonHom (o'.act.act a) := o'.act.hom
  obtain ⟨K, G, i, hG, hi, hfin, het, hpts⟩ :=
    exists_subgroup o.ab o'.ab o.ab hc ψ (o.act.act (algebraMap (𝓞 D.F) D.O α))
  have hnat : ∀ k : ℕ, o.act.act (k : D.O) = 𝟙 o.A ^ k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]
  have hcomb : ∀ {T : Over S} (x : T ⟶ o.A) (a u v : 𝓞 D.F), x ^ (p ^ E) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O (u * a + v * (p : 𝓞 D.F) ^ E)) = 1 := by
    intro T x a u v h1 h2
    rw [map_add, map_mul, map_mul, ← Nat.cast_pow, map_natCast, o.act.add, o.act.mul, o.act.mul, hnat,
      MonObj.comp_mul, ← Category.assoc, ← Category.assoc, h2, MonObj.comp_pow, Category.comp_id, h1,
      MonObj.one_comp, MonObj.one_comp, _root_.mul_one]
  have key : ∀ (T : Over S) (x : T ⟶ o.A),
      (x ≫ ψ = 1 ∧ ∃ e : ℕ, ES.KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
    intro T x
    rw [hpts]
    constructor
    · rintro ⟨h1, e, he⟩
      have h0 : x ^ (p ^ E) = 1 := by
        have : x ≫ ψ ≫ ψ' = 1 := by rw [← Category.assoc, h1, MonObj.one_comp]
        rwa [hψψ', MonObj.comp_pow, Category.comp_id] at this
      obtain ⟨a, ha, v, hv⟩ := hα2 e
      refine ⟨h0, h1, ?_⟩
      rw [hv, ← _root_.one_mul a]
      exact hcomb x a 1 v h0 (he a ha)
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h1, E, fun a ha => ?_⟩
      obtain ⟨u, v, rfl⟩ := hα1 a ha
      exact hcomb x α u v h0 h2
  refine ⟨K, G, i, hG, hi, hfin, het, fun a => ?_, ?_, key⟩
  · obtain ⟨h1, e, he⟩ := (key K i).2 ⟨𝟙 _, Category.id_comp _⟩
    refine (key K _).1 ⟨?_, e, fun z hz => ?_⟩
    · rw [Category.assoc, hlin, ← Category.assoc, h1, MonObj.one_comp]
    · rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, he z hz, MonObj.one_comp]
  · refine GlobalTheory.FinEtRank.isIsogDeg_of_card o.A K i hi hfin het _ ?_ fun k _ _ t => ?_
    · refine Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => ?_)
      have h := hu (p_mem_uIdeal D r)
      rw [Ideal.absNorm_eq_zero_iff.1 h0, Ideal.mem_bot] at h
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
    · haveI := charZero_of_isUnit b s hp k t
      obtain ⟨h1, h2⟩ := hT k t
      rw [hm, Nat.one_mul] at h2
      rw [← h2]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
      rw [← key]
      exact ⟨fun h => ⟨h.1, h1 g h.1 h.2⟩, fun h => ⟨h.1, 1, fun a ha => h.2 a (hu (by rwa [pow_one] at ha))⟩⟩

end GlobalTheory.UPel.HT.ES.KerUPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (z : Sp T.V ⟶ X.YY), (X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ z) → ∀ (k : X.F.J), ⊤ ≤ z ⁻¹ᵁ X.F.U k → ∀ (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr k (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t (some ⟨σ, i⟩) : T.Fr) := by
  first | exact @GlobalTheory.IntFrameDiag.diag_unit_of_intFr | exact GlobalTheory.IntFrameDiag.diag_unit_of_intFr | (intros; apply GlobalTheory.IntFrameDiag.diag_unit_of_intFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPointGenericFibreStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x : X) (φ : cR h x →+* 𝓞_ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ X), spMap φ ≫ cξ h x = yb → ∀ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : ((glueLB h).pull yb).Gen) (cc : ℂ_[p]ˣ), GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s (glueLB h) (sigGen h s) yb y e cc → ∃ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ ∧ ‖ψ (cu h x : Localization.Away (p : cR h x))‖ = ‖(cc : ℂ_[p])‖ := by
  first | exact @GlobalTheory.UnitGlue.EvalPt.evalPt_norm | exact GlobalTheory.UnitGlue.EvalPt.evalPt_norm | (intros; apply GlobalTheory.UnitGlue.EvalPt.evalPt_norm <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitoneStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A), Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) → (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A), (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) → (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) → ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | exact GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | (intros; apply GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckePointsPowEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_heckePoints_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u → u ^ k = 1 := by
  first | exact @GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_pow_eq_one | exact GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_pow_eq_one | (intros; apply GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_pow_eq_one <;> assumption)
end

