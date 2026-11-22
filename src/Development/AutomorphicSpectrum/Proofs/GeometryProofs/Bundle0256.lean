import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0254
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsEigFrameOfFrPt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

section Values

variable (T : Formalism.L2.Pj.CDVR)

theorem norm_eq_zpow {C : Type} [NormedField C] (j : T.Fr →+* C)
    (h1 : ∀ a : T.V, ‖j (algebraMap T.V T.Fr a)‖ ≤ 1) {π : T.V} (hπ : Irreducible π) {x : T.Fr} (hx : x ≠ 0) :
    ‖j x‖ = ‖j (algebraMap T.V T.Fr π)‖ ^ Formalism.L2.Pj.vV T.V x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  have hu : ‖j (algebraMap T.V T.Fr u)‖ = 1 := by
    have h : ‖j (algebraMap T.V T.Fr u)‖ * ‖j (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    refine le_antisymm (h1 _) ?_
    calc (1 : ℝ) = _ := h.symm
      _ ≤ ‖j (algebraMap T.V T.Fr u)‖ * 1 := mul_le_mul_of_nonneg_left (h1 _) (norm_nonneg _)
      _ = _ := mul_one _
  have hv : Formalism.L2.Pj.vV T.V (u • algebraMap T.V T.Fr π ^ n) = n := by
    rw [Formalism.L2.Pj.vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      GlobalTheory.PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit,
      GlobalTheory.PlaceCompletion.valV_algebraMap_of_irreducible hπ, _root_.one_mul, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp
  rw [hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow, hu, _root_.one_mul]

theorem norm_le_one_of_mem {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) (h : x ∈ 𝓞_ℂ_[p]) : ‖x‖ ≤ 1 := by
  suffices hs : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 from hs.1 h
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe,
    ← map_one (Valuation.RankOne.hom (PadicComplex.valued p).v),
    (Valuation.RankOne.strictMono _).le_iff_le, Valuation.restrict_le_one_iff]
  rfl

theorem exists_embed (hT : T.FinRes) :
    ∃ (p : Nat.Primes) (j : T.Fr →+* ℂ_[p]), ∀ a : T.Fr, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap T.V T.Fr).range := by
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
  have h1 : ∀ a : T.V, ‖k (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
    rw [← hk]
    exact (norm_le_one_of_mem _ (kO a).2)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hc0 : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hlt : ‖k (algebraMap T.V T.Fr π)‖ < 1 := by
    by_contra hc
    have he : ‖k (algebraMap T.V T.Fr π)‖ = 1 := le_antisymm (h1 π) (not_lt.mp hc)
    have := norm_eq_zpow T k h1 hπ (x := (p : T.Fr)) (Nat.cast_ne_zero.2 hp.out.ne_zero)
    rw [he, one_zpow, map_natCast] at this
    have h3 : ‖(p : ℂ_[p])‖ < 1 := by
      have e : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
      rw [e, norm_algebraMap']
      exact Padic.norm_p_lt_one
    exact h3.ne this
  have hpos : 0 < ‖k (algebraMap T.V T.Fr π)‖ := norm_pos_iff.2 ((map_ne_zero k).2
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hπ.ne_zero))
  refine ⟨⟨p, hp.out⟩, k, fun x => ⟨fun hx => ?_, by rintro ⟨a, rfl⟩; exact h1 a⟩⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  rcases ValuationRing.isInteger_or_isInteger T.V x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  · by_cases hu : IsUnit a
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨(u⁻¹ : T.Vˣ), ?_⟩
      have : algebraMap T.V T.Fr (u⁻¹ : T.Vˣ) * algebraMap T.V T.Fr u = 1 := by
        rw [← map_mul]; simp
      rw [ha] at this
      field_simp at this
      exact this
    · exfalso
      have hm : a ∈ Ideal.span {π} := by rw [← hπ.maximalIdeal_eq]; exact hu
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hm
      have h3 : ‖k x⁻¹‖ < 1 := by
        rw [← ha, map_mul, map_mul, norm_mul]
        calc _ ≤ ‖k (algebraMap T.V T.Fr π)‖ * 1 := mul_le_mul_of_nonneg_left (h1 b) (norm_nonneg _)
          _ < 1 := by simpa using hlt
      rw [map_inv₀, norm_inv] at h3
      have hp' : 0 < ‖k x‖ := norm_pos_iff.2 ((map_ne_zero k).2 h0)
      have := (inv_lt_one₀ hp').1 h3
      linarith

theorem exists_log_norm {C : Type} [NormedField C] (j : T.Fr →+* C)
    (hj : ∀ a : T.Fr, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap T.V T.Fr).range) :
    ∃ ρ : ℝ, ρ < 0 ∧ ∀ x : T.Fr, x ≠ 0 → Real.log ‖j x‖ = Formalism.L2.Pj.vV T.V x * ρ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have h1 : ∀ a : T.V, ‖j (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => (hj _).2 ⟨a, rfl⟩
  have hne : algebraMap T.V T.Fr π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hπ.ne_zero
  have hpos : 0 < ‖j (algebraMap T.V T.Fr π)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hne)
  have hlt : ‖j (algebraMap T.V T.Fr π)‖ < 1 := by
    refine lt_of_le_of_ne (h1 π) fun he => ?_
    have : ‖j (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, he, inv_one]
    obtain ⟨b, hb⟩ := (hj _).1 this
    refine hπ.not_isUnit (IsUnit.of_mul_eq_one b ?_)
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  refine ⟨Real.log ‖j (algebraMap T.V T.Fr π)‖, Real.log_neg hpos hlt, fun x hx => ?_⟩
  rw [norm_eq_zpow T j h1 hπ hx, Real.log_zpow]

end Values

section Pre

variable {S : Scheme.{0}} {A B G : Over S} [GrpObj G]

theorem pre_one (g : A ⟶ B) : g ≫ (1 : B ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (g ≫ toUnit B) (toUnit A)]

theorem pre_prod (g : A ⟶ B) {m : ℕ} (u : Fin m → (B ⟶ G)) :
    g ≫ (List.ofFn u).prod = (List.ofFn fun i => g ≫ u i).prod := by
  let f : (B ⟶ G) →* (A ⟶ G) :=
    { toFun := (g ≫ ·), map_one' := pre_one g, map_mul' := fun a b => by
        show g ≫ (a * b) = (g ≫ a) * (g ≫ b)
        rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift] }
  have := map_list_prod f (List.ofFn u)
  simpa [List.map_ofFn, f, Function.comp_def] using this

end Pre

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mult_conj (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) : D.mult (ComplexEmbedding.conjugate τ) = D.q := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hd' : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp [pow_two] at hre him
  have hr : H.rt0.re = 0 := by
    by_contra hne
    have h1 : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [h1] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  have hi : H.rt0.im ≠ 0 := by
    intro h1
    rw [hr, h1] at hre
    simp at hre
    exact H.d_prime.ne_zero hre
  unfold Datum.mult
  rw [if_neg]
  rw [ComplexEmbedding.conjugate_coe_eq, h]
  intro h2
  exact hi (by have := congrArg Complex.im h2; simp at this; linarith)

theorem exists_vecs {K : Type} [Field K] [Algebra c.F K] (z : Formalism.L2.Pj.FrPt Xo c K) {x : Sp K ⟶ Xo.X}
    (hx : x = z.x) (τ' : E →+* ℂ) {n : ℕ} (hn : D.mult τ' = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G), ∀ i, (v i).left = z.u τ' (i.cast hn.symm) := by
  subst hx
  exact ⟨fun i => Over.homMk (z.u τ' (i.cast hn.symm)) (z.tan τ' _).1, fun i => rfl⟩

theorem isEigFrame_of_frPt {K : Type} [Field K] [Algebra c.F K] (z : Formalism.L2.Pj.FrPt Xo c K) {x : Sp K ⟶ Xo.X}
    (hx : x = z.x) (τ' : E →+* ℂ) {n : ℕ} (hn : D.mult τ' = n) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (hv : ∀ i, (v i).left = z.u τ' (i.cast hn.symm)) :
    IsEigFrame Xo.univ.t.act x ((algebraMap c.F K).comp (tauIn c τ')) v := by
  subst hx
  subst hn
  have hv' : ∀ i, (v i).left = z.u τ' i := fun i => by simpa using hv i
  refine ⟨fun i => ⟨?_, fun a => ?_⟩, fun w hw => ?_⟩
  · show _ ≫ (v i).left = _
    rw [hv']
    exact (z.tan τ' i).2
  · rw [Over.comp_left, hv']
    exact z.eig τ' i a
  · have hb := z.basis τ' w.left ⟨Over.w w, hw.1⟩ (fun a => hw.2 a)
    obtain ⟨a, ⟨u, hu1, hu2⟩, huniq⟩ := hb
    refine ⟨a, ⟨u, fun i => ?_, ?_⟩, fun b hb => huniq b ?_⟩
    · rw [hv']; exact hu1 i
    · exact Over.OverMorphism.ext hu2.symm
    · obtain ⟨u', h1, h2⟩ := hb
      exact ⟨u', fun i => by rw [h1 i, hv']; rfl, congrArg (·.left) h2.symm⟩

theorem exists_cast {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (h : f = g)
    (m : SABMap t' t f) : ∃ m' : SABMap t' t g, m'.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_lift_int (T : Formalism.L2.Pj.CDVR) (f : 𝓞 E →+* T.Fr) :
    ∃ σ : 𝓞 E →+* T.V, (algebraMap T.V T.Fr).comp σ = f := by
  have h : ∀ a, f a ∈ (algebraMap T.V T.Fr).range := fun a => by
    have hi : IsIntegral ℤ a := RingOfIntegers.isIntegral a
    have hV : IsIntegral T.V (f a) := by
      obtain ⟨q, hqm, hq⟩ := hi
      refine ⟨q.map (Int.castRingHom T.V), hqm.map _, ?_⟩
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
        (f.comp (algebraMap ℤ (𝓞 E))), ← Polynomial.hom_eval₂, hq, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 hV
  let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective T.V T.Fr (congrArg Subtype.val hab),
      (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
  refine ⟨(e.symm : _ →+* _).comp (f.codRestrict _ h), RingHom.ext fun a => ?_⟩
  have := e.apply_symm_apply (f.codRestrict _ h a)
  exact congrArg Subtype.val this

theorem eps_hom (V : Type) [CommRing V] : spMap (algebraMap V (DualNumber V)) ≫ 𝟙 (Sp V) =
    spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) := by
  rw [Category.comp_id, Algebra.algebraMap_self, RingHom.comp_id]

theorem pt_hom (V : Type) [CommRing V] : spMap (algebraMap V V) = 𝟙 (Sp V) := by
  rw [Algebra.algebraMap_self]
  exact (congrArg Spec.map CommRingCat.ofHom_id).trans (Spec.map_id _)

def toAt (V : Type) [CommRing V] : epsOver V V ⟶ epsAt (𝟙 (Sp V)) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (eps_hom V))

def ofAt (V : Type) [CommRing V] : epsAt (𝟙 (Sp V)) ⟶ epsOver V V :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (eps_hom V).symm)

theorem ofAt_toAt (V : Type) [CommRing V] : ofAt V ≫ toAt V = 𝟙 _ :=
  Over.OverMorphism.ext (Category.comp_id _)

def ptAt (V : Type) [CommRing V] : Over.mk (𝟙 (Sp V)) ⟶ ptOver V V :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (pt_hom V))

theorem one_left_at (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] :
    (1 : Over.mk (𝟙 (Sp V)) ⟶ G).left = (1 : ptOver V V ⟶ G).left := by
  have h : ptAt V ≫ (1 : ptOver V V ⟶ G) = 1 := pre_one _
  rw [← h, Over.comp_left]
  exact Category.id_comp _

end Frames

end GlobalTheory.CompanionTheory.Ar.Flat.RuleVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.BaseExt

section Bundle

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

theorem normDegree_top_eq (M : HermitianBundle.{0} K) (M' : HermitianBundle.{0} L)
    (j : M.carrier → M'.carrier) (Φ : 𝓞 L ⊗[𝓞 K] M.carrier ≃ₗ[𝓞 L] M'.carrier)
    (hΦ : ∀ x, Φ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] x) = j x)
    (hm : ∀ (τ : L →+* ℂ) (x y : M.carrier),
      (M'.metric.form τ).inner ((1 : ComplexAt τ) ⊗ₜ[𝓞 L] j x) ((1 : ComplexAt τ) ⊗ₜ[𝓞 L] j y) =
        (M.metric.form (τ.comp (algebraMap K L))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 K] x) ((1 : ComplexAt _) ⊗ₜ[𝓞 K] y)) :
    M'.normDegree ⊤ = M.normDegree ⊤ := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have ht : LinearIndependent (𝓞 L) (fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) :=
    Module.Flat.linearIndependent_one_tmul (S := 𝓞 L) hs
  have hrank : Module.finrank (𝓞 L) (𝓞 L ⊗[𝓞 K] M.carrier) = Module.finrank (𝓞 K) M.carrier :=
    (TensorProduct.isBaseChange (𝓞 K) M.carrier (𝓞 L)).finrank_eq
  have hcomp : (Φ.toLinearMap ∘ fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) = fun i => j (s i) := by
    funext i
    simp [hΦ]
  have hs' : LinearIndependent (𝓞 L) (fun i => j (s i)) := by
    rw [← hcomp]
    exact ht.map' Φ.toLinearMap (LinearEquiv.ker Φ)
  have e1 : arithDegree M'.metric = arithDegree (M.metric.baseChange L) := by
    rw [arithDegree_eq M'.metric hs' (by rw [Fintype.card_fin, ← Φ.finrank_eq, hrank]),
      arithDegree_eq (M.metric.baseChange L) ht (by rw [Fintype.card_fin]; exact hrank.symm)]
    have hmap : (Submodule.span (𝓞 L) (Set.range fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)).map Φ.toLinearMap =
        Submodule.span (𝓞 L) (Set.range fun i => j (s i)) := by
      rw [Submodule.map_span, ← Set.range_comp, hcomp]
    have hg : ∀ τ : L →+* ℂ, gramDet M'.metric τ (fun i => j (s i)) =
        gramDet (M.metric.baseChange L) τ (fun i => (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) := by
      intro τ
      rw [LatticeLemmas.gramDet_baseChange]
      simp only [gramDet]
      congr 2
      ext a b
      simp only [Matrix.gram_apply]
      rw [fibreVec, fibreVec, fibreVec, fibreVec, FibreSpace.inner_equiv, FibreSpace.inner_equiv]
      exact hm τ _ _
    simp only [degreeWith, hg]
    rw [Nat.card_congr (Submodule.Quotient.equiv _ _ Φ hmap).toEquiv]
  have e2 := LatticeLemmas.BaseChange.proof K L M
  have e3 : M'.normDegree ⊤ = (M.baseChange L).deg := by
    rw [HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.deg]
    exact congrArg (· / (Module.finrank ℚ L : ℝ)) e1
  rw [e3, e2, HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.deg]

end Bundle

def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x x' : Sp R ⟶ S}
    (h : x = x') {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∃ M' : LieModel G x' V, ∀ e, lf (M'.pt e) = lf (M.pt e) := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    (dualMap c).comp (dualMap d) = dualMap (c.comp d) := by
  ext x <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨P, h⟩ := GlobalTheory.SabBaseChange.exists_prescribed f t
  obtain ⟨c, s, a, p, m, -⟩ := GlobalTheory.SabBaseChange.exists_pullback_prescribed f t P h
  exact ⟨_, ⟨m⟩⟩

variable {L : Type} [Field L] [NumberField L] {L' : Type} [Field L'] [NumberField L'] [Algebra L L']

theorem algebraMap_square :
    (algebraMap (𝓞 L') L').comp (algebraMap (𝓞 L) (𝓞 L')) = (algebraMap L L').comp (algebraMap (𝓞 L) L) := by
  ext x
  rfl

theorem exists_ext (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] :
    Nonempty (Σ D' : PPData H L', D.Ext D') := by
  obtain ⟨t', ⟨m₁⟩⟩ := exists_pull (spMap (algebraMap (𝓞 L) (𝓞 L'))) D.t
  obtain ⟨tK', ⟨m₂⟩⟩ := exists_pull (spMap (algebraMap (𝓞 L') L')) t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ D.t t' tK' _ _ m₁ m₂
  have hsq : spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) =
      spMap (algebraMap L L') ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp, spMap_comp, algebraMap_square]
  obtain ⟨m₃, -⟩ := sabCancel pullCubCancel E H _ _ _ D.t D.tK tK' _ (spMap (algebraMap L L')) D.m (hsq ▸ n)
  have pr : IsPrincipal tK' := (GlobalTheory.T.isPrincipal_base_change_iff E H L L' (algebraMap L L') D.tK tK' m₃).2 D.princ
  obtain ⟨B, MB, fib⟩ := GlobalTheory.T.principal_hermitian_fibre E H L' t' tK' m₂ pr
  exact ⟨⟨⟨t', tK', m₂, pr, B, MB, fib⟩, m₁⟩⟩

theorem ext_props (D : PPData H L) (D' : PPData H L') (m : D.Ext D') :
    D'.g = D.g ∧ D'.hp = D.hp ∧ ∃ io : D.B.carrier →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] D'.B.carrier,
      Function.Injective io ∧ Submodule.span (𝓞 L') (Set.range io) = ⊤ ∧
      ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier),
        ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) =
          ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x)
            ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  haveI : Smooth D'.t.G.hom := D'.t.semi.smooth
  obtain ⟨Mp, hMp⟩ := (LiePull.lieModel_pullback _ _ D.t.G D'.t.G (spMap (algebraMap (𝓞 L) (𝓞 L'))) m.φ m.cart (𝓞 L')
    (𝟙 _) D'.B.carrier).2 D'.MB
  obtain ⟨Mq, hMq⟩ := exists_transport
    (show 𝟙 _ ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) = spMap (algebraMap (𝓞 L) (𝓞 L')) ≫ 𝟙 _ by simp) Mp
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts _ D.t.G _ _ (algebraMap (𝓞 L) (𝓞 L')) (𝟙 _) _ _ D.MB Mq
  have hj' : ∀ e, (D'.MB.pt (j e)).left ≫ m.φ =
      spMap (dualMap (algebraMap (𝓞 L) (𝓞 L'))) ≫ (D.MB.pt e).left := by
    intro e
    have h1 : lf (Mq.pt (j e)) = spMap (dualMap (algebraMap (𝓞 L) (𝓞 L'))) ≫ (D.MB.pt e).left :=
      (Category.comp_id _).symm.trans (hj e)
    rw [hMp, ← h1]
    exact (hMq _).symm
  letI : Module (𝓞 L) D'.B.carrier := Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))
  haveI : IsScalarTower (𝓞 L) (𝓞 L') D'.B.carrier := ⟨fun a b x => by
    change (a • b) • x = algebraMap (𝓞 L) (𝓞 L') a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let jl : D.B.carrier →ₗ[𝓞 L] D'.B.carrier :=
    { toFun := j, map_add' := j.map_add, map_smul' := fun r x => j.map_smulₛₗ r x }
  have hb : IsBaseChange (𝓞 L') jl := GlobalTheory.T.lie_model_isBaseChange _ D.t.G _ _ (𝟙 _) _ _ D.MB Mq jl hj
  have hΦ : ∀ x, hb.equiv ((1 : 𝓞 L') ⊗ₜ[𝓞 L] x) = j x := fun x => by
    rw [hb.equiv_tmul, one_smul]
    rfl
  have hmet : ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier),
      ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j y) : ℂ) =
        ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x)
          ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
    intro σ' x y
    obtain ⟨M₁, h₁⟩ := GlobalTheory.T.lie_model_complex_base_change _ D.t.G L (𝟙 _) D.B.carrier D.MB (σ'.comp (algebraMap L L'))
    obtain ⟨M₂, h₂⟩ := GlobalTheory.T.lie_model_complex_base_change _ D'.t.G L' (𝟙 _) D'.B.carrier D'.MB σ'
    have a := D.fib (σ'.comp (algebraMap L L')) x y _ _ (h₁ x) (h₁ y)
    have b := D'.fib σ' (j x) (j y) _ _ (h₂ (j x)) (h₂ (j y))
    have hring : (σ'.comp (algebraMap (𝓞 L') L')).comp (algebraMap (𝓞 L) (𝓞 L')) =
        (σ'.comp (algebraMap L L')).comp (algebraMap (𝓞 L) L) := by
      rw [RingHom.comp_assoc, algebraMap_square, RingHom.comp_assoc]
    have hz : spMap ((σ'.comp (algebraMap L L')).comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
        (spMap (σ'.comp (algebraMap (𝓞 L') L')) ≫ 𝟙 _) ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) := by
      rw [Category.comp_id, Category.comp_id, spMap_comp, hring]
    obtain ⟨M₃, h₃⟩ := exists_transport hz M₁
    have hv : ∀ e, (M₂.pt ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j e)).left ≫ m.φ =
        (M₃.pt ((1 : ComplexAt _) ⊗ₜ[𝓞 L] e)).left := by
      intro e
      have c₁ : lf (M₂.pt ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] j e)) =
          spMap (dualMap (σ'.comp (algebraMap (𝓞 L') L'))) ≫ (D'.MB.pt (j e)).left :=
        (Category.comp_id _).symm.trans (h₂ (j e))
      have c₂ : lf (M₁.pt ((1 : ComplexAt _) ⊗ₜ[𝓞 L] e)) =
          spMap (dualMap ((σ'.comp (algebraMap L L')).comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt e).left :=
        (Category.comp_id _).symm.trans (h₁ e)
      change lf _ ≫ m.φ = lf _
      rw [h₃, c₁, c₂, Category.assoc, hj', ← Category.assoc, spMap_comp, dualMap_comp, hring]
    have T := GlobalTheory.T.hodge_inner_product_pullback_unique E H _ _ D'.t D.t _ m (spMap (σ'.comp (algebraMap (𝓞 L') L')) ≫ 𝟙 _) _ _ _ _ (hv x) (hv y)
    exact T.2 _ _ ((T.1 _).1 b) (hodge_congr _ hz (h₃ _).symm (h₃ _).symm a)
  refine ⟨hb.finrank_eq, ?_, j, ?_, ?_, hmet⟩
  · have := normDegree_top_eq D.B D'.B j hb.equiv hΦ hmet
    simp only [PPData.hp, this]
  · intro x y hxy
    have h1 : (1 : 𝓞 L') ⊗ₜ[𝓞 L] x = (1 : 𝓞 L') ⊗ₜ[𝓞 L] y := hb.equiv.injective (by rw [hΦ, hΦ, hxy])
    have hinj : Function.Injective ((Algebra.linearMap (𝓞 L) (𝓞 L')).rTensor D.B.carrier) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective _ _)
    have h2 : (1 : 𝓞 L) ⊗ₜ[𝓞 L] x = (1 : 𝓞 L) ⊗ₜ[𝓞 L] y := hinj (by simpa using h1)
    simpa using congrArg (TensorProduct.lid (𝓞 L) D.B.carrier) h2
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨t, rfl⟩ := hb.equiv.surjective y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [hb.equiv_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    | add a b ha hb' =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb'

end GlobalTheory.CompanionTheory.Ar.Sl.BaseExt

open GlobalTheory.CompanionTheory.Ar.Sl.BaseExt in

theorem GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'], Nonempty (Σ D' : PPData H L', D.Ext D') ∧ ∀ (D' : PPData H L') (_ : D.Ext D'), D'.g = D.g ∧ D'.hp = D.hp ∧ ∃ io : D.B.carrier →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] D'.B.carrier, Function.Injective io ∧ Submodule.span (𝓞 L') (Set.range io) = ⊤ ∧ ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier), ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) = ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
  intro E _ _ _ H L _ _ D L' _ _ _
  exact ⟨exists_ext D L', fun D' m => ext_props D D' m⟩
end
end

