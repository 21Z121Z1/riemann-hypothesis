import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas
import Formalism.LocalToGlobal.Columns.Bundle0006
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Columns.HeckeInert
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
import Formalism.LocalToGlobal.Columns.RowFormsLemmas

-- bundled from Formalism.LocalToGlobal.Columns.DiamondPreservesRamified
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

theorem Deco.IsDnA.dia1 {P : ST} {q : 𝓞 E} {a : 𝓞 E ⧸ P.1.asIdeal} {d d' : Deco E n ST SG}
    (h : Deco.IsDnA P q a d d') (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    Deco.IsDnA P q (c.1 * a) d (d'.dia (Pi.mulSingle P c)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · ext1
    · have h5 := congrArg Deco.N h1
      exact h5
    · funext Q y
      have h3 : d'.f Q = (d.dn P (d'.f P)).f Q := by rw [← h1]
      simp only [Deco.dia, Deco.dn] at h3 ⊢
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Function.update_self]
      · rw [Function.update_of_ne hQ]
        rw [Function.update_of_ne hQ] at h3
        rw [h3, Pi.mulSingle_eq_of_ne hQ, Units.val_one, one_mul]
    · have h6 := congrArg Deco.be h1
      exact h6
  · intro e he hfe
    show ((Pi.mulSingle P c : DiaG E ST) P).1 * d'.f P (q • e) = c.1 * a
    rw [Pi.mulSingle_eq_same, h2 e he hfe]

theorem Deco.L_dia (d : Deco E n ST SG) (c : DiaG E ST) : (d.dia c).L = d.L := by
  unfold Deco.L
  congr 1
  ext x
  show (x ∈ d.N ∧ ∀ P : ST, (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ ∀ P : ST, d.f P x = 0)
  simp only [Units.mul_right_eq_zero]

theorem Deco.Lsh_dia (d : Deco E n ST SG) (c : DiaG E ST) : (d.dia c).Lsh = d.Lsh := by
  unfold Deco.Lsh
  rw [Deco.L_dia]

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

theorem colDel_dia (u : Pr.Word) (j : ℕ) (c : DiaG X.E (Pr.vT u)) (d : (colGSD W Ch u j).D) :
    (colGSD W Ch u j).Del (c • d) = (colGSD W Ch u j).Del d := by
  show delAtr X.emb (W.lamTrue u j) (d.1.dia c).Lsh = delAtr X.emb (W.lamTrue u j) d.1.Lsh
  rw [Deco.Lsh_dia]

end Cols

section Adj

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Adj

section AtW

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem TUmC_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    TUmC W Ch u w = 1 := by
  unfold TUmC UprodC expTc
  rw [VVTc_of_seenBarC W hPr u w h, topsP_of_seenBarC W hPr u w h]
  simp

theorem NlamG_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    NlamG W Ch u w = MramL W Ch u := by
  ext φ
  show (φ : MfV W Ch u) ∈ scaledRamifiedLattice W Ch u w ↔ (φ : MfV W Ch u) ∈ MfL W Ch u
  unfold scaledRamifiedLattice
  rw [TUmC_of_seenBarC W Ch hPr u w h]
  constructor
  · rintro ⟨ψ, hψ, e⟩
    have e' : ψ = (φ : MfV W Ch u) := e
    rw [← e']
    exact hψ.1
  · intro hφ
    exact ⟨φ, ⟨hφ, φ.2⟩, rfl⟩

end AtW

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.GoodXgTie
section
open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Comparison₂

variable {X : Fields} (Pr : Primes X) {m : ℕ} (Ch : Chars X Pr m) (r : ℕ) [∀ i, Fact (Pr.g i).Prime]
  (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ) (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i))

def XgGreenOk : Prop :=
  ∀ i : Fin 2, (∀ x y : Formalism.CyclotomicNorms.Fbar (Pr.g i), x ≠ 0 → y ≠ 0 → teich i x = teich i y → x = y) ∧
    Formalism.L2.NT.IsGenSys (ζ i)

def gxGoodIrrC : Set (G0 X.E Pr.vGs r → ℂ) :=
  {χc | Formalism.L2.NT.IsIrrChar χc ∧ gxGood Pr Ch r σ teich ζ χc}

def XgCTie : Prop :=
  (∃ z : X.K, IsPrimitiveRoot z (Fintype.card (G0 X.E Pr.vGs r))) →
    (((XgC Pr Ch r σ teich ζ).image fun χ x => σ (χ x) : Finset (G0 X.E Pr.vGs r → ℂ)) : Set (G0 X.E Pr.vGs r → ℂ)) =
      gxGoodIrrC Pr Ch r σ teich ζ

def XgNonempty : Prop := Pr.Ok → Ch.Ok → XgGreenOk Pr teich ζ → (∀ i, 3 ≤ Pr.g i) → 9 ≤ r → 2 ≤ X.f →
  (∃ z : X.K, IsPrimitiveRoot z (Fintype.card (G0 X.E Pr.vGs r))) → (XgC Pr Ch r σ teich ζ).Nonempty

end Comparison₂

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.HeckeInertLemmas
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.inertSet_finite {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d : DecoSet E n ST SG) :
    (d.inertSet P s).Finite := by
  have hPk : P ^ s.sum ≠ ⊥ := pow_ne_zero _ hP
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPk
  have hI : Ideal.span {a} * P ^ s.sum ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hPk⟩
  have hfin := finite_between ((Ideal.span {a} * P ^ s.sum) • d.1.N) d.1.N
    (finite_quot_smul d.1.N d.2.lat.fg _ hI)
  refine Set.Finite.of_injOn (f := fun e : DecoSet E n ST SG => Ideal.span {a} • e.1.N) ?_ ?_ hfin
  · intro e he
    obtain ⟨h1, h2⟩ := he.1.smul_le
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact Submodule.smul_mono le_rfl h1
    · exact (Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem _).2 haP) le_rfl).trans h2
  · intro e he e' he' h
    have hN : e.1.N = e'.1.N := by
      simp only [Submodule.ideal_span_singleton_smul] at h
      have hinj : Function.Injective fun x : Sp E n => a • x := smul_right_injective (Sp E n) ha
      have hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B := by
        intro A B hAB x hx
        have : a • x ∈ a • B := hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx
        obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        rwa [← hinj hyx]
      exact le_antisymm (hsub _ _ h) (hsub _ _ h.symm)
    exact Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))

theorem DecoSet.mem_inertNb {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d e : DecoSet E n ST SG) :
    e ∈ d.inertNb P s ↔ e ∈ d.inertSet P s := by
  unfold DecoSet.inertNb
  rw [dif_pos (DecoSet.inertSet_finite hP s d), Set.Finite.mem_toFinset]

theorem DecoSet.sum_inertNb_smul {M : Type} [AddCommMonoid M] (P : Ideal (𝓞 E)) (s : List ℕ)
    (g : UF E n × GLG E n SG) (d : DecoSet E n ST SG) (ψ : DecoSet E n ST SG → M) :
    ∑ e ∈ (g • d).inertNb P s, ψ e = ∑ e ∈ d.inertNb P s, ψ (g • e) := by
  symm
  exact Finset.sum_equiv (MulAction.toPerm g) (fun e => (DecoSet.smul_mem_inertNb_iff g).symm) (fun e _ => rfl)

end Fin

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Op

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_asAlgebraHom_eq (a : MonoidAlgebra K A) : ρ.asAlgebraHom a = ∑ t : A, a.coeff t • ρ t := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp [Finsupp.sum_fintype]

theorem rf_coord_act (t : A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ t φ) = ((S.toCSD h).actMat (S.repCSD h ρ) t).mulVec (S.coordOf h S.outSec φ) := by
  have c : ∀ x, S.coordOf h S.outSec x = ⇑((S.toCSD h).basis.repr (S.res h x)) := fun x => rfl
  have e1 : (S.repCSD h ρ) t (S.res h φ) = S.res h (ρ t φ) := by
    show (S.res h) (ρ t ((S.res h).symm (S.res h φ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [c, c]
  unfold CSD.actMat
  rw [LinearMap.toMatrix_mulVec_repr, e1]

theorem rf_coord_ga (a : MonoidAlgebra K A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ.asAlgebraHom a φ) =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVec (S.coordOf h S.outSec φ) := by

  have hsum : ∀ {m : ℕ} (M : A → Matrix (Fin m) (Fin m) K) (c : A → K) (v : Fin m → K),
      (∑ t, c t • M t).mulVec v = ∑ t, c t • (M t).mulVec v := by
    intro m M c v
    rw [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply]
  rw [rf_asAlgebraHom_eq, LinearMap.sum_apply, map_sum]
  unfold CSD.gaMat
  rw [hsum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [LinearMap.smul_apply, map_smul, rf_coord_act]

theorem rf_range_ga (a : MonoidAlgebra K A) :
    (LinearMap.range (ρ.asAlgebraHom a)).map (S.coordOf h S.outSec).toLinearMap =
      LinearMap.range ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin := by
  have e : (S.coordOf h S.outSec).toLinearMap ∘ₗ ρ.asAlgebraHom a =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin ∘ₗ (S.coordOf h S.outSec).toLinearMap := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    exact rf_coord_ga S h ρ a φ
  rw [← LinearMap.range_comp, e, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

private theorem range_subE_lemma {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (Z : Submodule K (Fin n → K)) :
    LinearMap.range (subE Z).mulVecLin = Z := by
  rw [Matrix.range_mulVecLin]
  have e : (subE Z).col = ⇑Z.subtype ∘ ⇑(subBasis Z) := by
    funext j i
    rfl
  rw [e, Set.range_comp, Submodule.span_image, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem invariantSubspace_coords_X (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : (mtildeKGSD W Ch sel mu).Ok) :
    (V0X W Ch sel mu Xg P).map ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).toLinearMap =
      LinearMap.range ((V0C W Ch sel mu h Xg P).E).mulVecLin := by
  unfold V0X
  rw [rf_range_ga]
  exact (range_subE_lemma _).symm

end Rows

section LvlPart

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_mem_lvlPart_iff (P : Subgroup A) (ψ : P →* Kˣ) (φ : S.EqFun) :
    S.coordOf h S.outSec φ ∈ (S.toCSD h).lvlPart (S.repCSD h ρ) P ψ ↔
      ∀ a : P, ρ (a : A) φ = ((ψ a : Kˣ) : K) • φ := by
  show (∀ a : P, ((S.toCSD h).actMat (S.repCSD h ρ) (a : A)).mulVec (S.coordOf h S.outSec φ) =
      ((ψ a : Kˣ) : K) • S.coordOf h S.outSec φ) ↔ _
  refine forall_congr' (fun a => ?_)
  rw [← rf_coord_act, ← map_smul]
  exact (S.coordOf h S.outSec).injective.eq_iff

end LvlPart

section RowsLvl

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem mem_lvlPartX_iff (h : (mtildeKGSD W Ch sel mu).Ok) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec φ ∈
        (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr ↔
      φ.1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine Iff.trans ?_ (mem_MtildeV_iff W Ch sel mu P φ.1).symm
  exact (rf_mem_lvlPart_iff _ h (g0HatRepEqFunX W Ch sel mu) P.grp P.chr φ).trans ⟨fun H => ⟨φ.2, H⟩, fun ⟨_, H⟩ => H⟩

end RowsLvl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RowFormsRank
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

open Classical in

def GSD.orbFun (d : S.D) (v : S.V) (x : S.D) : S.V := if hx : ∃ g : S.G, g • d = x then S.ρ hx.choose v else 0

variable {S}

theorem GSD.rho_eq_of_fixed {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) {g₁ g₂ : S.G}
    (e : g₁ • d = g₂ • d) : S.ρ g₁ v = S.ρ g₂ v := by
  have h1 : (g₂⁻¹ * g₁) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 : S.ρ g₁ = S.ρ g₂ * S.ρ (g₂⁻¹ * g₁) := by rw [← map_mul, mul_inv_cancel_left]
  rw [h2, Module.End.mul_apply, hv _ h1]

theorem GSD.orbFun_smul {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) (g : S.G) :
    S.orbFun d v (g • d) = S.ρ g v := by
  have hx : ∃ g' : S.G, g' • d = g • d := ⟨g, rfl⟩
  unfold GSD.orbFun
  rw [dif_pos hx]
  exact GSD.rho_eq_of_fixed hv hx.choose_spec

theorem GSD.orbFun_mem {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) : S.orbFun d v ∈ S.EqFun := by
  intro g x
  by_cases hx : ∃ g' : S.G, g' • d = x
  · obtain ⟨g', rfl⟩ := hx
    rw [← mul_smul, GSD.orbFun_smul hv, GSD.orbFun_smul hv, map_mul, Module.End.mul_apply]
  · have hx' : ¬ ∃ g' : S.G, g' • d = g • x := by
      rintro ⟨g', e⟩
      exact hx ⟨g⁻¹ * g', by rw [mul_smul, e, inv_smul_smul]⟩
    unfold GSD.orbFun
    rw [dif_neg hx, dif_neg hx', map_zero]

theorem GSD.finrank_pos_iff (h : S.Ok) :
    0 < finrank K S.EqFun ↔ ∃ (d : S.D) (v : S.V), v ≠ 0 ∧ ∀ g : S.G, g • d = d → S.ρ g v = v := by
  have := S.finiteDimensional_EqFun h
  rw [Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨φ, hφ⟩
    have : ∃ d, (φ : S.D → S.V) d ≠ 0 := by
      by_contra hc
      exact hφ (Subtype.ext (funext fun d => by
        by_contra hd
        exact hc ⟨d, hd⟩))
    obtain ⟨d, hd⟩ := this
    refine ⟨d, _, hd, fun g hg => ?_⟩
    have := φ.2 g d
    rw [hg] at this
    exact this.symm
  · rintro ⟨d, v, hv0, hv⟩
    refine ⟨⟨S.orbFun d v, GSD.orbFun_mem hv⟩, fun e => hv0 ?_⟩
    have h1 : S.orbFun d v ((1 : S.G) • d) = 0 := congrFun (congrArg Subtype.val e) ((1 : S.G) • d)
    rw [GSD.orbFun_smul hv, map_one] at h1
    exact h1

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def RowsNonzero (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  0 < finrank X.K (MtildeV W Ch sel mu P) ∧ ∀ j, 1 ≤ j → j ≤ R.m → 0 < finrank X.K (MtV W Ch sel mu P j)

end Rows

end Formalism.L2.Col
end
end

