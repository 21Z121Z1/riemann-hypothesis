import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0037
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0019
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverShortThetaValueData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H) :
    Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h2 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h2
    have h3 : (l.M : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr (by have := l.three_le; omega)
    exact h3 h2
  have : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot l.Mb hne
  have : Module.Finite (𝓞 E) Dw.La := Dw.fin
  have : Module.Finite (𝓞 E ⧸ l.Mb) (LevQ Dw l) :=
    Module.Finite.of_restrictScalars_finite (𝓞 E) (𝓞 E ⧸ l.Mb) (LevQ Dw l)
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

theorem exists_cover_shortVal_data :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y'.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y'.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (z i b) (tp q b) (F q i b)) := by
  intro hL E _ _ _ H Dw l Xo c n Λ N hU hT hN S _ _ y
  have hN0 : 0 < N := hN.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := le_trans hN.2.2 inf_le_left
  have hlev : ∀ {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ Xo.X) (x' : Sp R' ⟶ Xo.X)
      (h : ptO Xo x' ⟶ ptO Xo x) (a : Dw.La), h ≫ levPt Xo x a = levPt Xo x' a := by
    intro R R' _ _ x x' h a
    rw [levPt, levPt, ← Category.assoc, comp_toUnit]
  have hkill : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), KilledBy Xo l.Mb (levPt Xo x a) := by
    intro R _ x a b hb
    rw [levPt, Category.assoc, (moduli_univ_eta_killed hL E H Dw l Xo a).1 b hb, MonObj.comp_one]
  have hpowM : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ l.M = 1 := by
    intro R _ x a
    rw [levPt, ← MonObj.comp_pow, (moduli_univ_eta_killed hL E H Dw l Xo a).2.2, MonObj.comp_one]
  have hpowN : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ N = 1 := by
    intro R _ x a
    obtain ⟨k, hk⟩ := hN.2.1
    rw [hk, pow_mul, hpowM, one_pow]
  have : Finite (LevQ Dw l) := finite_levQ Dw l
  let _ : Fintype ((Fin n → LevQ Dw l) × Fin n) := Fintype.ofFinite _
  obtain ⟨B1, _, φ1, w, hφ1, hw⟩ := GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion hL E H Dw l Xo S y.x N l.M hN0
    (by have := l.three_le; omega) ((Fin n → LevQ Dw l) × Fin n)
    (fun j => levPt Xo y.x (levRep (j.1 j.2))) (fun j => hpowM _ _)
  have hw' : ∀ j, w j ^ N = levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2)) := by
    intro j
    apply Over.OverMorphism.ext
    rw [hw j, ← hlev y.x (spMap φ1 ≫ y.x) (Over.homMk (spMap φ1) rfl), Over.comp_left]
    rfl
  have hroot := fun j => (exists_root_killedBy_pow E H Dw l Xo (ptO Xo (spMap φ1 ≫ y.x))
    (levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2))) (w j) N hN0 (hkill _ _) (hw' j)).1
  choose tp1 htp1 htp1k using hroot
  obtain ⟨B2, _, φ2, z, hφ2, hz, hzg⟩ := GlobalTheory.T.exists_faithfullyFlat_split_isotropicGroup hL E H Dw l Xo B1 (spMap φ1 ≫ y.x) n Λ N hU hN0 hle
  let _ : Algebra c.F B2 := ((φ2.comp φ1).comp (algebraMap c.F S)).toAlgebra
  let φA : S →ₐ[c.F] B2 := { toRingHom := φ2.comp φ1, commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c S B2 φA y
  have hyx : y'.x = spMap φ2 ≫ spMap φ1 ≫ y.x := by
    rw [hy'.1, ← Category.assoc, FramedBaseChange.spMap_spMap]
  let hA : ptO Xo y'.x ⟶ ptO Xo (spMap φ1 ≫ y.x) := Over.homMk (spMap φ2) hyx.symm
  let hB : ptO Xo y'.x ⟶ ptO Xo (spMap φ2 ≫ spMap φ1 ≫ y.x) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact hyx.symm)
  have hI := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  have hz' : ∀ i, InZh Xo Λ N (fun b => hB ≫ z i b) := fun i => hI.1 _ _ hB (z i) (hz i)
  have htpN : ∀ q b, (hA ≫ tp1 (q, b)) ^ N = levPt Xo y'.x (levRep (q b)) := by
    intro q b
    rw [← MonObj.comp_pow, htp1, hlev]
  have hUU := (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hN.1 (ptO Xo y'.x) y'.s).2
  have hF : ∀ (q : Fin n → LevQ Dw l) (i : Fin (Λ.zCard N (Dw.p + Dw.q))) (b : Fin n), ∃ F,
      IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (hB ≫ z i b) (hA ≫ tp1 (q, b)) F := by
    intro q i b
    refine (hUU _ _ ((hz' i).1 b) ?_).exists
    rw [pow_two, pow_mul, htpN, hpowN]
  choose F hF using hF
  refine ⟨B2, inferInstance, inferInstance, φA, y', fun i b => hB ≫ z i b, fun q b => hA ≫ tp1 (q, b), F,
    RingHom.FaithfullyFlat.stableUnderComposition φ1 φ2 hφ1 hφ2, hy', hz', ?_, ?_, hF⟩
  · exact hI.2.2.1 B2 B2 _ y'.x (RingHom.id B2) hB
      (Spec.map_id (CommRingCat.of B2)).symm _ z hzg
  · intro q b
    obtain ⟨j, hj⟩ := htp1k (q, b)
    exact ⟨htpN q b, j, fun a ha => by rw [Category.assoc, hj a ha, MonObj.comp_one]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.RunIn.WtSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_cm {M : Type} [AddCommMonoid M] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (g : (E →+* ℂ) → M) :
    ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) = ∑ τ, g τ := by
  classical
  have hs : ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) =
      ∑ τ ∈ X.Ψ, (g τ + g (ComplexEmbedding.conjugate τ)) :=
    Finset.sum_coe_sort X.Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ))
  rw [hs, Finset.sum_add_distrib, ← Finset.sum_add_sum_compl X.Ψ g]
  congr 1
  refine Finset.sum_nbij' (fun τ => ComplexEmbedding.conjugate τ) (fun τ => ComplexEmbedding.conjugate τ)
    ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    simpa [Finset.mem_compl] using (X.cmType τ).1 hτ
  · intro τ hτ
    have h1 : τ ∉ X.Ψ := by simpa [Finset.mem_compl] using hτ
    by_contra h2
    exact h1 ((X.cmType τ).2 (by simpa using h2))
  · intro τ _
    simp
  · intro τ _
    simp
  · intro τ _
    rfl

theorem two_mul_card_cm {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * Fintype.card X.Ψ = Module.finrank ℚ E := by
  have h := sum_cm X (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ, ← h]
  ring

theorem sum_row_le (r p0 : ℕ) (hp : p0 ≤ r) (u v : ℕ → ℕ) :
    ∑ j : Fin r, (if p0 ≤ (j : ℕ) then u ((j : ℕ) - p0) else v (p0 - 1 - (j : ℕ))) ≤
      ∑ i ∈ Finset.range r, u i + ∑ i ∈ Finset.range r, v i := by
  classical
  rw [Finset.sum_ite]
  gcongr
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ)), u ((j : ℕ) - p0)
          = ∑ i ∈ Finset.image (fun j : Fin r => (j : ℕ) - p0) (Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ))), u i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, u i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, _, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ)), v (p0 - 1 - (j : ℕ))
          = ∑ i ∈ Finset.image (fun j : Fin r => p0 - 1 - (j : ℕ)) (Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ))), v i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, v i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, hj, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega

theorem spread_le {r : ℕ} (x b : Fin r → ℝ) (m : ℝ) (hm : 0 ≤ m) (hb : ∀ i, 0 ≤ b i)
    (hx : ∀ i, |x i| = b i + m) : (⨆ i, x i) - ⨅ i, x i ≤ ∑ i, b i + 2 * m := by
  classical
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · rw [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
    have : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb i)
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi, ← hj]
    have hxi : x i ≤ b i + m := (le_abs_self _).trans (hx i).le
    have hxj : -(b j + m) ≤ x j := by
      have := neg_abs_le (x j)
      rw [hx j] at this
      exact this
    by_cases hij : i = j
    · subst hij
      have : 0 ≤ ∑ k, b k := Finset.sum_nonneg (fun k _ => hb k)
      linarith
    · have hpair : b i + b j ≤ ∑ k, b k := by
        rw [← Finset.sum_pair hij]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hb k)
      linarith

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_bijective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Bijective (relab (E := E) c σ) := by
  have hinj : Function.Injective (relab (E := E) c σ) := by
    intro τ τ' hττ'
    unfold relab embF at hττ'
    ext x
    have h1 := congrArg (fun f : E →+* ℂ => f x) hττ'
    simp only [RingHom.comp_apply] at h1
    exact congrArg Subtype.val (σ.injective h1)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

private lemma entry_abs (p0 j s t h : ℕ) :
    |(((if p0 ≤ j then (s : ℤ) + (h : ℤ) else -(t : ℤ) - (h : ℤ) : ℤ)) : ℝ)| =
      (((if p0 ≤ j then s else t : ℕ)) : ℝ) + (h : ℝ) := by
  split_ifs with hj
  · push_cast
    exact abs_of_nonneg (by positivity)
  · push_cast
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) h])]
    ring

theorem laU_bounds (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (B : ℕ)
    (hB : ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) ≤ B) :
    (∑ τ, (U.X k).spread (laU U a n k) τ) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n ∧
      (∑ τ, ∑ i, |((laU U a n k τ i : ℤ) : ℝ)|) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
  unfold laU
  have hp : (U.X k).p0 ≤ r := (U.X k).p0_le
  have hbij := relab_bijective (E := E) c σ
  have hm2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    exact_mod_cast this
  have htot : ∑ τ : (U.X k).Ψ, (∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) ≤ B := by
    have hinvb : Function.Bijective (Function.invFun (relab (E := E) c σ)) :=
      ⟨(Function.rightInverse_invFun hbij.2).injective, (Function.leftInverse_invFun hbij.1).surjective⟩
    calc _ = ∑ τ : (U.X k).Ψ, ((fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ.1 +
            (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) (ComplexEmbedding.conjugate τ.1)) := rfl
      _ = ∑ τ, (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ :=
          sum_cm (U.X k) (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i))
      _ = ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) := Fintype.sum_bijective _ hinvb _ _ (fun _ => rfl)
      _ ≤ B := hB
  have hsum : ∑ τ : (U.X k).Ψ, ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) ≤ (B : ℝ) := by
    calc _ ≤ ∑ τ : (U.X k).Ψ, (((∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro τ _
          rw [← Nat.cast_sum]
          exact_mod_cast sum_row_le r (U.X k).p0 hp (fun i => a (Function.invFun (relab c σ) τ.1, i))
            (fun i => a (Function.invFun (relab c σ) (conjEmb τ.1), i))
      _ ≤ (B : ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast htot
  have h0 : (0 : ℝ) ≤ Fintype.card (U.X k).Ψ := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  constructor
  · calc _ ≤ ∑ τ : (U.X k).Ψ, (∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + 2 * ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro τ _
          unfold ReciprocityTheory.ChartRestriction.G.FD.Data.spread
          exact spread_le _ _ _ (by positivity) (fun j => by positivity) (fun j => entry_abs _ _ _ _ _)
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 h0]
  · calc _ = ∑ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro τ _
          apply Finset.sum_congr rfl
          intro j _
          exact entry_abs _ _ _ _ _
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
          have e : ∀ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) = ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + r * ((n / 2 : ℕ) : ℝ) := by
            intro τ
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_congr rfl (fun τ _ => e τ), Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 (mul_nonneg h0 hr0)]

theorem sum_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (m : ℕ) :
    ∑ τ, ∑ i ∈ Finset.range m, wtA w (τ, i) ≤ WeightAlgebra.DF w := by
  classical
  unfold wtA WeightAlgebra.DF WeightAlgebra.degP ext0
  have key : ∀ (q : ℕ) (g : Fin q → ℕ),
      ∑ i ∈ Finset.range m, (if h : i < q then g ⟨i, h⟩ else 0) ≤ ∑ i, g i := by
    intro q g
    calc _ ≤ ∑ i ∈ Finset.range q, (if h : i < q then g ⟨i, h⟩ else 0) := by
          apply Finset.sum_le_sum_of_ne_zero
          intro i _ hi
          rw [Finset.mem_range]
          by_contra hc
          exact hi (dif_neg hc)
      _ = ∑ i, g i := by
          rw [Finset.sum_range]
          simp
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_le_sum (fun t _ => ?_)
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact add_le_add (key _ _) (key _ _)

theorem laU_wtA_size : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * w.n ∧ (∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * D.R.r * w.n / 2 := by
  intro D T h j hj w σ hσ k
  have h2 := two_mul_card_cm ((T.U j σ).X k)
  have h3 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h4 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.der.finrank_E
    rw [h4]
    simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hc : (Fintype.card ((T.U j σ).X k).Ψ : ℝ) = D.R.f := by
    have : Fintype.card ((T.U j σ).X k).Ψ = D.R.f := by omega
    exact_mod_cast this
  have hb := laU_bounds (T.U j σ) (wtA w) w.n k (WeightAlgebra.DF w) (sum_wtA_le w _)
  rw [hc] at hb
  exact hb

end GlobalTheory.RunIn.WtSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaSumEqOfWitnessesCommonAlgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  have hx : w.x = spMap ψ.toRingHom ≫ y.x := by
    unfold FrMap at hm
    exact hm.1
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx.symm
  have hh : h.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm h hh
  have hpull : ∀ q i b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G)
      (whiskerRight_snd _ _) (F q i b) (GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) :=
    fun q i b => GlobalTheory.VVRank.isPullSec_pullS _ _ h _
  obtain ⟨hZ, -, hG, -⟩ := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b,
    fun q i b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b),
    fun i => hZ _ _ h _ (hz i), hG S T y.x w.x ψ.toRingHom h hh _ z hg, fun q b => ⟨?_, ?_⟩,
    fun q i b => (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊥ _ _ h y.s w.s hs
      (F q i b) _ (hpull q i b)).2 (z i b) (tp q b) (hF q i b), fun q => ?_⟩
  · dsimp only
    rw [← MonObj.comp_pow, (ht q b).1]
    unfold levPt
    rw [← Category.assoc, toUnit_unique (h ≫ toUnit _) (toUnit _)]
  · obtain ⟨j, hj⟩ := (ht q b).2
    refine ⟨j, ?_⟩
    unfold KilledBy at hj ⊢
    intro x hx
    rw [Category.assoc, hj x hx, MonObj.comp_one]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.T.harmonicValue_baseChange_alt hC E H Dw l Xo c nab hnab S T ψ y w hm h hh a n P hP N (F q i)
      (fun b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) (hpull q i)

theorem eq_of_local {K T : Type} [Field K] [CommRing T] [Algebra K T] (u v : T)
    (h : ∀ (U : Type) [CommRing U] [IsLocalRing U] [Algebra K U] (κ : T →ₐ[K] U), κ u = κ v) : u = v := by
  rw [← sub_eq_zero]
  refine eq_zero_of_localization (u - v) fun J hJ => ?_
  have := hJ.isPrime
  have e := h (Localization.AtPrime J) (IsScalarTower.toAlgHom K T (Localization.AtPrime J))
  simpa [map_sub, sub_eq_zero] using e

theorem shortSum_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → FrMap φ2 y y2 → (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y1.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y1.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y1.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y2.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y2.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y2.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ∀ q, ψ1 (∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) * ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b)) = ψ2 (∑ i, ∑ m ∈ P.support, algebraMap c.F S2 (P.coeff m) * ∏ b, nab y2 ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hUn hTr hLev a P hP S _ _ y S1 _ _ φ1 y1 z1 tp1 F1
    S2 _ _ φ2 y2 z2 tp2 F2 hm1 hm2 hz1 hg1 ht1 hF1 hz2 hg2 ht2 hF2 T _ _ ψ1 ψ2 hψ q
  refine eq_of_local (K := c.F) _ _ fun U _ _ _ κ => ?_
  obtain ⟨yU, hyU⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S U ((κ.comp ψ1).comp φ1) y
  have e : (κ.comp ψ1).comp φ1 = (κ.comp ψ2).comp φ2 := by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hψ]
  have hU1 : FrMap (κ.comp ψ1) y1 yU := GlobalTheory.FramedBaseChange.cancel φ1 (κ.comp ψ1) hm1 hyU
  have hU2 : FrMap (κ.comp ψ2) y2 yU := GlobalTheory.FramedBaseChange.cancel φ2 (κ.comp ψ2) hm2 (e ▸ hyU)
  obtain ⟨z1', tp1', F1', hz1', hg1', ht1', hF1', hs1⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ1) y1 yU hU1 z1 tp1 F1 hz1 hg1 ht1 hF1
  obtain ⟨z2', tp2', F2', hz2', hg2', ht2', hF2', hs2⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ2) y2 yU hU2 z2 tp2 F2 hz2 hg2 ht2 hF2
  have key := GlobalTheory.T.isotropicSum_independent_of_choices_local hL E H Dw l Xo c nab hnab n Λ N hUn hTr hLev P U yU z1' tp1' F1' z2' tp2' F2'
    hz1' hg1' ht1' hF1' hz2' hg2' ht2' hF2' q
  have h1 := hs1 q
  have h2 := hs2 q
  simp only [AlgHom.comp_apply] at h1 h2
  rw [h1, h2]
  exact key

end GlobalTheory.ShortCompare
end
end

