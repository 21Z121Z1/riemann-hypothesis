import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0263
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open Formalism.UG.P
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdComp

theorem eq_zero_of_valued_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (x : P.adicCompletion E) (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
  have h1 := h (m.natAbs + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_eps_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) : adAt F w (afsplitEps E v) = 1 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 1))
    (fun n => by
      rw [he]
      exact hspec _ 1 w n (by rw [h, afsplitI_self, map_one, sub_self, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_one, map_one] at h0
  exact h0

theorem adAt_eps_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) : adAt F w (afsplitEps E v) = 0 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 0))
    (fun n => by
      rw [he]
      exact hspec _ 0 w n (by rw [afsplitI_ne v _ h, map_zero, sub_zero, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_zero, map_zero] at h0
  exact h0

theorem adAt_eps_mul_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = adAt F w z := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_under v w h, one_mul]

theorem adAt_eps_mul_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = 0 := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_ne v w h, zero_mul]

theorem prV_zero_int_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  intro F E _ _ _ _ _ v z
  classical
  have hinj : ∀ x y : E ⊗[F] v.adicCompletion F, afsplitIE v x = afsplitIE v y → x = y := by
    intro x y hxy
    rw [← afsplit_prV_IE v x, hxy, afsplit_prV_IE]
  have hdec : afsplitIE v (prV (E := E) v z) = afsplitEps E v * z := afsplit_decomp v z
  have hz : ∀ w : HeightOneSpectrum (𝓞 E), adAt F w (0 : AfE F E) = 0 := by
    intro w; unfold adAt; exact map_zero _
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 E),
      adAt F w (afsplitEps E v * z) = if w.under (𝓞 F) = v then adAt F w z else 0 := by
    intro w
    split_ifs with hw
    · exact adAt_eps_mul_of_under v w hw z
    · exact adAt_eps_mul_of_ne v w hw z
  refine ⟨⟨fun h0 w hw => ?_, fun h => ?_⟩, ⟨fun hint w hw => ?_, fun h => ?_⟩⟩
  · rw [← adAt_eps_mul_of_under v w hw z, ← hdec, h0, map_zero, hz]
  · apply hinj
    rw [hdec, map_zero]
    apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [hcomp, hz]
    split_ifs with hw
    · exact h w hw
    · rfl
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [← hdec]; exact afsplit_IE_int v _ hint
    rw [← adAt_eps_mul_of_under v w hw z]
    exact (mem_rInt_iff F E _).mp h1 w
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [mem_rInt_iff]
      intro w
      change Valued.v (adAt F w (afsplitEps E v * z)) ≤ 1
      rw [hcomp]
      split_ifs with hw
      · exact h w hw
      · rw [map_zero]; exact zero_le'
    have h2 := afsplit_prV_int v _ h1
    rwa [← hdec, afsplit_prV_IE] at h2

end GlobalTheory.Mem.Col2.AdComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimesOverPlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem conjO_piG_ne (hPr : Pr.Ok) (a : Fin 2) : X.conjO (Pr.piG a) ≠ 0 := by
  intro h0
  have := hPr.piG_norm a
  rw [h0, mul_zero] at this
  exact (Nat.cast_ne_zero.2 (hPr.g_prime a).ne_zero) this.symm

theorem mem_vG_iff (hPr : Pr.Ok) (a : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Pr.vG a ↔ X.conjO (Pr.piG a) ∈ P.asIdeal := mem_divs (conjO_piG_ne hPr a) P

theorem g_mem_of_isOver {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)}
    (hv : IsOver v P) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ((Pr.g a : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [hv, Ideal.mem_comap, map_natCast] at h
  exact h

theorem eq_of_isOver (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) {P Q : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) (hQ : Q ∈ Pr.vGs)
    (hPv : IsOver v P) (hQv : IsOver v Q) : Q = P := by
  rcases rll_over_cases hc hPv hQv with e | e
  · exact e
  exfalso
  have hPa := mem_vG_of_g_mem hPr hP (g_mem_of_isOver hPv h)
  have hQa := mem_vG_of_g_mem hPr hQ (g_mem_of_isOver hQv h)
  rw [mem_vG_iff hPr] at hPa hQa
  rw [e, mem_conjP] at hQa
  have h2 : cO X.E (X.conjO (Pr.piG a)) = Pr.piG a := RingOfIntegers.ext (star_star _)
  rw [h2] at hQa
  obtain ⟨x, y, hxy⟩ := hPr.piG_cop a
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ hQa) (Ideal.mul_mem_left _ _ hPa)

theorem exists_over_vGs (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ∃ w : {w // w ∈ Pr.vGs}, IsOver v w.1 := by
  have h01 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  have hv : v ∈ plUnder X.F Pr.vGs := by
    rw [plUnder_vGs hc hPr v]
    rcases h01 a with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨P, hP, hPv⟩ := hv
  exact ⟨⟨P, hP⟩, hPv⟩

theorem isOver_of_under {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : P.under (𝓞 X.F) = v) :
    IsOver v P := by
  subst h
  rfl

theorem under_of_isOver {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : IsOver v P) :
    P.under (𝓞 X.F) = v :=
  HeightOneSpectrum.ext h.symm

end GlobalTheory.Mem.TypePrimes

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem residue_natCast (hPr : Pr.Ok) {a : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG a)
    (c : 𝓞 X.E ⧸ w.asIdeal) : ∃ k : ℕ, c = k := by
  haveI : NeZero (Pr.g a) := ⟨(hPr.g_prime a).ne_zero⟩
  have e := (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime a) (by
    rw [← hPr.vG_norm a w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  exact ⟨(e.symm c).val, by rw [← map_natCast e, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]⟩

theorem vG_disjoint (hPr : Pr.Ok) : Disjoint (Pr.vG 0) (Pr.vG 1) := by
  rw [Finset.disjoint_left]
  intro w h0 h1
  have hc : IsCoprime ((Pr.g 0 : ℕ) : 𝓞 X.E) ((Pr.g 1 : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime 0) (hPr.g_prime 1)).2 hPr.g_ne)
  obtain ⟨x, y, hxy⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h0)) (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h1))

theorem primes_over_places : ∀ (X : Fields) (Pr : Primes X) (hc : Formalism.BasicNotions.CMData X.F X.E), Pr.Ok →
    ∃ wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs},
      (∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h) ∧
      (∀ a v h, (∀ P : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = v → X.conjO (Pr.piG a) ∈ P.asIdeal →
          P = (wOf a v h).1) ∧ (wOf a v h).1.under (𝓞 X.F) = v ∧
        ∀ c : 𝓞 X.E ⧸ (wOf a v h).1.asIdeal, ∃ k : ℕ, c = k) ∧
      ∀ φ : {w // w ∈ Pr.vGs} → ℂ, ∏ w, φ w =
        ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) := by
  intro X Pr hc hPr
  classical
  let wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs} :=
    fun a v h => (exists_over_vGs hc hPr h).choose
  have hspec : ∀ a v h, IsOver v (wOf a v h).1 := fun a v h => (exists_over_vGs hc hPr h).choose_spec
  have h1 : ∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h := by
    intro a v h w
    constructor
    · intro hw
      exact Subtype.ext (eq_of_isOver hc hPr h (wOf a v h).2 w.2 (hspec a v h) hw)
    · rintro rfl
      exact hspec a v h
  have hin : ∀ a v h, (wOf a v h).1 ∈ Pr.vG a := fun a v h =>
    mem_vG_of_g_mem hPr (wOf a v h).2 (g_mem_of_isOver (hspec a v h) h)
  refine ⟨wOf, h1, fun a v h => ⟨?_, under_of_isOver (hspec a v h), residue_natCast hPr (hin a v h)⟩, ?_⟩
  · intro P hPu hP
    have hPa : P ∈ Pr.vG a := (mem_vG_iff hPr a P).2 hP
    exact eq_of_isOver hc hPr h (wOf a v h).2 (mem_vGs hPa) (hspec a v h) (isOver_of_under hPu)
  · intro φ
    let φ' : HeightOneSpectrum (𝓞 X.E) → ℂ := fun w => if hw : w ∈ Pr.vGs then φ ⟨w, hw⟩ else 1
    have hL : ∏ w, φ w = ∏ w ∈ Pr.vGs, φ' w := by
      rw [← Finset.prod_coe_sort Pr.vGs φ']
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [φ', dif_pos w.2]
    have hA : ∀ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) =
        ∏ w ∈ Pr.vG a, φ' w := by
      intro a
      let f : HeightOneSpectrum (𝓞 X.F) → ℂ := fun v => if h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal then φ (wOf a v h) else 1
      have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h)) = ∏ᶠ v, f v := by
        refine finprod_congr fun v => ?_
        exact finprod_eq_dif _
      have hsupp : Function.mulSupport f ⊆ ((Pr.vG a).image fun w => w.under (𝓞 X.F) : Finset _) := by
        intro v hv
        have h' : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal := by
          by_contra hn
          exact hv (by simp only [f, dif_neg hn])
        rw [Finset.coe_image]
        exact ⟨(wOf a v h').1, hin a v h', under_of_isOver (hspec a v h')⟩
      rw [e1, finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_image]
      · refine Finset.prod_congr rfl fun w hw => ?_
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        have hw' : w ∈ Pr.vGs := mem_vGs hw
        have e2 : wOf a (w.under (𝓞 X.F)) hg = ⟨w, hw'⟩ :=
          ((h1 a _ hg ⟨w, hw'⟩).1 (isOver_of_under rfl)).symm
        simp only [f, φ', dif_pos hg, dif_pos hw', e2]
      · intro w hw w' hw' he
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        exact (eq_of_isOver hc hPr hg (mem_vGs hw) (mem_vGs hw') (isOver_of_under rfl) (isOver_of_under he.symm)).symm
    rw [hL, Fin.prod_univ_two, hA 0, hA 1]
    unfold Primes.vGs
    exact Finset.prod_union (vG_disjoint hPr)

end GlobalTheory.Mem.TypePrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

theorem conjSplit_w (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    (conjSplit s).w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f f' : GAf L n → W) :
    NG.heckeD J Dset (f + f') = NG.heckeD J Dset f + NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : GAf L n → W,
      Function.support (fun cc : GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply]
  simp only [NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem heckeD_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n)) :
    NG.heckeD J Dset (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem tN_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite) {m : ℕ} (F : Fin m → GAf L n → W) :
    NG.tN J s ϖ k (∑ j, F j) = ∑ j, NG.tN J s ϖ k (F j) := by
  classical
  have key : ∀ t : Finset (Fin m), NG.tN J s ϖ k (∑ j ∈ t, F j) = ∑ j ∈ t, NG.tN J s ϖ k (F j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [NG.tN, heckeD_zero]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [NG.tN]
      rw [heckeD_add L n J _ hfin, smul_add]
  exact key Finset.univ

theorem prod_eq_vieta (n : ℕ) (β : Multiset ℂ) (hn : Multiset.card β = n) :
    (β.map fun a => X - C a).prod = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * β.esymm k) * X ^ (n - k) := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hn, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton,
    Multiset.prod_zero, Multiset.sum_singleton, map_one, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr (by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega) fun k _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, mul_assoc]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem cls_heq {E : Type} [Field E] [NumberField E] {n : ℕ} {a b : HeightOneSpectrum (𝓞 E)} (h : a = b)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (a.adicCompletion E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (b.adicCompletion E)))
    (he : HEq σ.cl τ.cl) : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls τ) := by
  subst h
  exact heq_of_eq (congrArg (Sigma.mk n) (eq_of_heq he))

theorem galSide (hL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {n : ℕ}
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (α : Fin n → ℂˣ) (hα : GlobalTheory.SmGL.HasSatake σ.ρ α) :
    ((GlobalTheory.CuspRep.ParLaws.locRec hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).unr ∧
    ((GlobalTheory.CuspRep.ParLaws.locRec hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).frobEig = twEig w α := by
  rw [GlobalTheory.CuspRep.ParLaws.rec_eq_diag (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL h) hα]
  have hu : (GlobalTheory.WeilDeligne.WD.mk (GlobalTheory.WeilDeligne.WDRep.diag h fun i => (α i)⁻¹)).unr :=
    (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _)
  refine ⟨(GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 hu, ?_⟩
  rw [GlobalTheory.WeilDeligne.WD.frobEig_tw _ _ hu, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  simp [twEig]

theorem heckeSide (hL : GlobalTheory.Published.LocalLanglandsGL) {L : Type} [Field L] [NumberField L] [IsCMField L] {Ω : Type}
    [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω} {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (hu : IsUnif L s.v ϖ) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) (f : GAf L n → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) (c : ℕ → ℂ)
    (hc : ∀ k, 1 ≤ k → k ≤ n → NG.tN J s ϖ k f = c k • f) (hp : IsPlaceOver A (conjSplit s).w)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSplit s).w.adicCompletion L))) (hσ : IsLocS π.S (conjSplit s) σ) :
    ∃ α, GlobalTheory.SmGL.HasSatake σ.ρ α ∧ ∀ k, 1 ≤ k → k ≤ n →
      ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k = (twEig (conjSplit s).w α).esymm k := by
  obtain ⟨i, T, hic, hcomp, hinj, hmem, heq⟩ := hσ
  have hf' := GlobalTheory.T.autRep_isotypic_splitPlace_localComponent L n π (conjSplit s) σ i T hinj hmem heq f hf
  obtain ⟨m, Tj, ej, hTj, hej, hsum⟩ := GlobalTheory.T.splitPlace_fixed_vector_sum_spherical_images L n π (conjSplit s) σ i hic hcomp f hf' hfix
  have hne : ∃ j, ej j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [hsum]
    simp [h]
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    obtain ⟨j, hj⟩ := hne
    exact (Submodule.ne_bot_iff _).2 ⟨ej j, hej j, hj⟩
  have hR := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL hp
  obtain ⟨α, hα⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake_of_unr hR ((GlobalTheory.CuspRep.ParLaws.unr_iff hR σ).2 hsph)
  refine ⟨α, hα, fun k hk1 hk2 => ?_⟩
  have hfin := GlobalTheory.T.finite_heckeDoubleCoset_cosets_at_splitPlace L n s ϖ hu J hJ k
  have key : ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k f =
      (twEig (conjSplit s).w α).esymm k • f := by
    conv_lhs => rw [hsum]
    rw [tN_sum J s ϖ k hfin, Finset.smul_sum, hsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ =>
      GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical L n s ϖ hu J hJ σ α hα i hic hcomp (Tj j) (hTj j) (ej j) (hej j) k hk1 hk2
  rw [hc k hk1 hk2, smul_smul] at key
  exact smul_left_injective ℂ hf0 key

theorem locPol_eq : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) → ∀ x, GlobalTheory.AutQuot.LocAt π w x →
    ((GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).unr ∧
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      (Multiset.map (fun α => X - Polynomial.C α)
        ((GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).frobEig).prod := by
  intro hL D π s w ϖ hcw hu J hJ f hf hf0 hfix c hc x hx
  have hw := conjSplit_w D s w hcw
  subst hw
  obtain ⟨σc, hσc, huniq⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV π (conjSplit s)
  obtain ⟨s', σ', h', hσ', hxe⟩ := hx
  have hh := huniq π s' h' σ' (NG.AutRep.iso_equivalence.refl π) hσ'
  have hxc : x = GlobalTheory.LocLanglands.cls σc := eq_of_heq (hxe.symm.trans (cls_heq h' σ' σc hh))
  subst hxc
  obtain ⟨α, hα, heig⟩ := heckeSide hL π s ϖ hu J hJ f hf hf0 hfix c hc (D.nd.plOm.2 _) σc hσc
  obtain ⟨hun, hfe⟩ := galSide hL (D.nd.plOm.2 _) σc α hα
  refine ⟨hun, ?_⟩
  rw [hfe, prod_eq_vieta D.R.nV _ (by simp [twEig])]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  rw [mul_assoc, heig k hk1 hk2]

end

end GlobalTheory.HeckeFrob

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplittingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_finite_selfDualLattice_splitting : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) → ∀ (sS : Fam S) (sT : Fam T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) ΛS ΛS → GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T k') ΛT ΛT → ∀ x y : (AE D)ˣ, FinUnit x → FinUnit y → IsDetRoot S k x → IsDetRoot T k' y → om (k, k') f = ((((χT x)⁻¹ * χS y : Circle)) : ℂ) • f := by
  first | exact @GlobalTheory.FinVac.om_vacuum_finite | exact GlobalTheory.FinVac.om_vacuum_finite | (intros; apply GlobalTheory.FinVac.om_vacuum_finite <;> assumption)
end

