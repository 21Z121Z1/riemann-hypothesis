import Formalism.LocalToGlobal.Columns.UnfoldingPhiCompLeftUnipotentSource
import Formalism.LocalToGlobal.Columns.FreePointColumnFormula
import Formalism.LocalToGlobal.Columns.ReductionColumnStandardBasis
import Formalism.LocalToGlobal.Columns.Bundle0059

-- bundled from Formalism.LocalToGlobal.Columns.ClXQSrcEvHolds
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

theorem clS_card {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
  unfold qOf
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem clS_covS : TruncatedUnfoldingChangeOfVarsSource := by
  intro E _ _ _ P K _ n' c' n c hc hp hu psi D a b e hadd hint Ψ hsupp haD hinv r hr g hg hx hre _ heD A B hA hB _ wt y
  subst hc
  exact clS_cov (ciQ_mem P) hu hp (clS_card P) psi D a b e hadd hint Ψ hsupp haD hinv hr hg hx hre heD A B hA hB wt y

section Close

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_xiLawQ_ofT {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ} (hCT : TruncatedUnfoldingChangeOfVarsTarget)
    (hok : L.Ok Ch sel mu cst G m2) (hd : ∀ w : rowSG Pr sel mu, w.1 ∉ Pr.vGs → TwDegOne X w.1)
    (hb : ∀ j (b : L.β j) (w : rowSG Pr sel mu), w.1 ∉ Pr.vGs → TwBdd (Pr := Pr) j w.1 (L.h j b w))
    (hD : ∀ w : rowSG Pr sel mu, w.1 ∉ Pr.vGs → m2 ≤ cst.D w) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) :
    XiLawQ Ch sel mu cst L i al be :=
  clXQ_xiLawQ_of hCT clS_covS hok hd hb hD hi al be

end Close

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.CqCard
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem cq_card {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
  unfold qOf
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem cq_covT : TruncatedUnfoldingChangeOfVarsTarget := by
  intro E _ _ _ P K _ n' c' n c hc hp hu psi D a b e hadd hint Ψ hsupp haD hinv r hr g hgI hg hre _ heD A B hA hbB _ wt y
  subst hc
  exact finite_sum_target_equality (ciQ_mem P) hu hp (cq_card P) psi hadd hint Ψ hsupp haD hinv r hr g hgI hg hre heD hA hbB wt y

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.QthConjClose
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Conj

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : (q : E) ≠ 0)

def QClose {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m) : Prop :=
  ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E)

theorem qth_conj_close {m : ℕ} (h r : Sp E m ≃ₗ[E] Sp E m) (a b N e : ℕ)
    (ha : ∀ i j, P.valuation E (((toGLm E m h : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ≤ WithZero.exp (a : ℤ))
    (hb : ∀ i j, P.valuation E (((toGLm E m h⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ≤ WithZero.exp (b : ℤ))
    (hr : ∀ i j, P.valuation E ((((toGLm E m r : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ WithZero.exp (-(N : ℤ)))
    (he : WithZero.exp (-(e : ℤ)) ≤ P.valuation E (q : E)) (hN : a + b + e ≤ N) : QClose P q (h⁻¹ * r * h) := by
  intro i j
  set A := ((toGLm E m h⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hAdef
  set R := ((toGLm E m r : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hRdef
  set B := ((toGLm E m h : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hBdef
  have hmul : ((toGLm E m (h⁻¹ * r * h) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) = A * R * B := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  have hAB : A * B = 1 := by
    rw [hAdef, hBdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have key : A * R * B - 1 = A * (R - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  rw [hmul, key]
  have h1 := qth_conj_le P A (R - 1) B (b : ℤ) (a : ℤ) (N : ℤ) hb hr ha i j
  refine h1.trans (le_trans ?_ he)
  exact WithZero.exp_le_exp.mpr (by omega)

include hq0 in

theorem qth_mem_JQ {n c : ℕ} (kj : ℕ) (y : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hy : QClose P q y) (hy' : QClose P q y⁻¹) :
    y ∈ LocE.JQ P q kj n c := by
  have hinv : ∀ x : Sp E (n + c), y⁻¹ (y x) = x := fun x => LinearEquiv.symm_apply_apply y x
  have he : ∀ l : ℕ, (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 0 ∨
      (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 1 := by
    intro l
    simp only
    split_ifs <;> simp
  refine Subgroup.mem_inf.2 ⟨fun x => ⟨fun hx => ?_, fun hx => qth_close_std P q hq0 y hy hx⟩,
    fun x => ⟨fun hx => ?_, fun hx => qth_close_scl P q hq0 _ he y hy hx⟩⟩
  · have := qth_close_std P q hq0 y⁻¹ hy' hx
    rwa [hinv] at this
  · have := qth_close_scl P q hq0 _ he y⁻¹ hy' hx
    rwa [hinv] at this

include hq0 in

theorem qth_red_entry (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) {m : ℕ} {y : Sp E m ≃ₗ[E] Sp E m} (hy : QClose P q y) (i j : Fin m) :
    IntAt P (((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ∧
      redP P (((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) = redP P ((1 : Matrix (Fin m) (Fin m) E) i j) := by
  set M := ((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hMdef
  have hyij : P.valuation E ((M - 1) i j) ≤ P.valuation E (q : E) := hy i j
  have hv0 : P.valuation E (q : E) ≠ 0 := by simpa using hq0
  have ha0 : P.valuation E ((1 : Matrix (Fin m) (Fin m) E) i j) ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hd : IntAt P ((M - 1) i j / (q : E)) := by
    rw [qth_intAt_iff, map_div₀, div_eq_mul_inv]
    calc P.valuation E ((M - 1) i j) * (P.valuation E (q : E))⁻¹
        ≤ P.valuation E (q : E) * (P.valuation E (q : E))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hv0
  have hsum : M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (q : E) * ((M - 1) i j / (q : E)) := by
    rw [mul_div_cancel₀ _ hq0, Matrix.sub_apply]
    ring
  refine ⟨?_, ?_⟩
  · rw [qth_intAt_iff, show M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (M - 1) i j by
      rw [Matrix.sub_apply]; ring]
    exact Valuation.map_add_le _ ha0 (hyij.trans (qth_vq_le P q))
  · rw [hsum]
    exact redP_add_natCast_mul hq hd

end Conj

end Formalism.L2.Col
end
end

