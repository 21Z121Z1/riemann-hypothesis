import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstJetTermsGaugeUnitMulBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

private theorem pre_lemma {Z Y X : Scheme.{0}} (x : Z ⟶ Y) (y : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ⊤ ≤ (x ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (show x.base p ∈ (⊤ : Y.Opens) from trivial)
  exact this

private theorem norm_natCast_le_one_kummer_theta_logarithms {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (f : Γ(X, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := pre_lemma _ _ _ h
  unfold valR
  rw [dif_pos h, dif_pos h']
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h (by intro _ _; trivial)]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e5 := fun w => congrArg (fun g => CommRingCat.Hom.hom g w) e2
  simp only [Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e5
  simp only [spMap, CommRingCat.hom_comp, RingHom.comp_apply, ← e5]
  congr 1

private theorem univ_le_preimage_inf_of_univ_le {Z X : Scheme.{0}} (y : Z ⟶ X) (U V : X.Opens) (h1 : ⊤ ≤ y ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := by
  intro p hp
  exact ⟨h1 hp, h2 hp⟩

private theorem alg_lemma_5 {S : Type} [CommRing S] {n : ℕ} (a b : Fin n → S) (Ps g1 g2 g T : S)
    (h : Ps * (g1 * g2) = T) : (∑ i, a i * (Ps * b i)) * (g1 * (g2 * g)) = T * ∑ i, a i * (b i * g) := by
  rw [← h, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private theorem mul_prod_four_rearrange {S : Type} [CommRing S] (a0 a1 a2 a3 b0 b1 b2 b3 : S) :
    a0 * a1 * a2 * a3 * (b0 * b1 * b2 * b3) = (a0 * b2) * (a1 * b0) * (a2 * b1) * (a3 * b3) := by
  ring

theorem jc_eq_unit_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  intro R _ _ D C _ _ N ν gm₀ gm htan hpull k J hJ
  have hb : gm.b.left = spMap (dualMap (toF R C)) ≫ gm₀.b.left := hpull.1
  have hν : ∀ (P : Sp (DualNumber C) ⟶ D.P.A.left), ⊤ ≤ P ⁻¹ᵁ D.P.L.U (ν.J (redE C ≫ P)) :=
    fun P => GlobalTheory.T.dualNumber_field_point_mem_open_of_reduction C P _ (ν.good _)
  have hQ : redE C ≫ gm.b.left = (TF (R := R) C).hom ≫ eSec D.P.A := by
    rw [hb, ← Category.assoc, gl_redE, Category.assoc, gl_tan D gm₀ htan, ← gl_TF R C]
  have hJb : ∀ (p : Sp (DualNumber R) ⟶ D.P.A.left), ⊤ ≤ (spMap (dualMap (toF R C)) ≫ p) ⁻¹ᵁ D.P.L.U (J p) :=
    fun p => pre_lemma _ _ _ (hJ p)
  have hc0 : ⊤ ≤ gm.b.left ⁻¹ᵁ (D.P.L.U (ν.J (redE C ≫ gm.b.left)) ⊓ D.P.L.U (J gm₀.b.left)) :=
    univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb]; exact hJb _)
  have hcR : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left) :=
    top_le_wchart _ _ _ _ (fun _ => by rw [Category.id_comp, ← gl_tan D gm₀ htan]; exact pre_lemma _ _ _ (hJ _))
  refine ⟨(isUnit_trV D.P.L gm.b.left _ _ hc0 (k : ℤ)).unit, ?_, ?_, ?_⟩
  · unfold TanExp.rigValD valR
    rw [dif_pos hcR]
    exact (((D.rig.s _).isUnit.map _).map _).ne_zero
  · rw [IsUnit.unit_spec]
    have e1 : (trV D.P.L gm.b.left (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ)).fst =
        trV D.P.L (redE C ≫ gm.b.left) (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ) := by
      unfold trV
      exact (norm_natCast_le_one_kummer_theta_logarithms (TrivSqZeroExt.fstHom C C C).toRingHom _ _ _ hc0).symm
    have e2 : toF R C (TanExp.rigValD D (J gm₀.b.left)) = valR (TF (R := R) C).hom
        (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left)) (D.rig.s fun _ => J gm₀.b.left).val := by
      unfold TanExp.rigValD
      rw [gl_TF R C]
      have h5 := norm_natCast_le_one_kummer_theta_logarithms (toF R C) (𝟙 _) _ (D.rig.s fun _ => J gm₀.b.left).val hcR
      rw [Category.comp_id] at h5
      exact h5.symm
    have hQ1 : ⊤ ≤ ((TF (R := R) C).hom ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U (J gm₀.b.left) := by
      rw [← hQ, hb, ← Category.assoc]; exact pre_lemma _ _ _ (hJ _)
    have e3 := GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) C).hom
      (fun _ => ν.J ((TF (R := R) C).hom ≫ eSec D.P.A)) (fun _ => J gm₀.b.left)
      (top_le_wchart _ _ _ _ (fun _ => ν.good _)) (top_le_wchart _ _ _ _ (fun _ => hQ1))
    rw [e1, e2, hQ]
    simp only [NumOf.rg, vF]
    unfold valF
    unfold valR at e3 ⊢
    rw [e3]
    simp only [Finset.univ_unique, Finset.prod_singleton, mul_pow]
    rw [trV_pow D.P.L _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (ν.good _) hQ1), _root_.one_mul]
  · intro s n c f hlin α
    have hyP : ∀ {Z : Scheme.{0}} (g : D.P.A.left ⟶ Z),
        (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left ≫
          (D.prB C).left ≫ g = gm.b.left ≫ g :=
      fun g => by rw [← Category.assoc, gl_prB']
    have hsec := GlobalTheory.T.sectionValue_linear_relation_linComb D.P.L (D.famφ C (ν.eX α)) (DegPre.famε k) (s.s (ν.eX α)) (D.famφB (ν.eX α))
      (DegPre.famε k) (fun i => f i (ν.eX α)) (D.prB C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))
      (hlin _)
      (fun i => ν.J (redE C ≫ (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C)
        gm.b).left ≫ D.famφ C (ν.eX α) i))
      (fun i => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
      (by
        intro k₁ k₂ e
        rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢
        · rw [e]
        · rw [← hyP, ← e]
        · rw [← hyP, e]
        · rw [← hyP, ← hyP, e])
      (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left
      (top_le_wchart _ _ _ _ (fun i => hν _))
      (top_le_wchart _ _ _ _ (fun i => by rw [gl_prB']; exact hν _))
    have hS : ∀ i, valR gm.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
        ((f i (ν.eX α)).f fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j)) =
        (∏ j, trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) j) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
          (J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) (DegPre.famε k j)) *
        dualMap (toF R C) (valR gm₀.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
          ((f i (ν.eX α)).f fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))) := by
      intro i
      have hA : ⊤ ≤ gm₀.b.left ⁻¹ᵁ LB.wchart D.P.L (D.famφB (ν.eX α)) (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) :=
        top_le_wchart _ _ _ _ (fun j => hJ _)
      rw [GlobalTheory.T.sectionValue_linComb_change_of_charts D.P.L (D.famφB (ν.eX α)) (DegPre.famε k) (f i (ν.eX α)) gm.b.left _
        (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
        (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [hb, Category.assoc]; exact hJb _))]
      congr 1
      rw [hb]
      exact norm_natCast_le_one_kummer_theta_logarithms _ _ _ _ hA
    have hφ : ∀ j, D.gtφT (TE R C) gm.b (ν.eX α) j = spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j :=
      fun j => gl_gtφT_pull D (epsR R) (TE R C) (spMap (dualMap (toF R C))) (gl_hom R C) gm₀.b gm.b hb (ν.eX α) j
    have hpj : ∀ j, ⊤ ≤ D.gtφT (TE R C) gm.b (ν.eX α) j ⁻¹ᵁ D.P.L.U (pickJ (D.gtφT (TE R C) gm.b (ν.eX α))
        (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j) := by
      intro j
      obtain ⟨i', he, hj⟩ := pickJ_spec (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j
      rw [hj, ← he, hφ i']
      exact hJb _
    unfold jc sE vE
    rw [hsec]
    simp only [gl_scal, gl_prB', hS]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε (gm.s (ν.eX α)) (gm.3 _) (𝟙 _) _
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))]
    rw [gl_corr D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε
      (fun j => spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j) DegPre.gtε _ _ (hpull.2 _)
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (fun k₁ k₂ e => pickJ_congr _ _ e)
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ, hφ]; exact e))
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ k₂]; exact e))
      (𝟙 _)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [gl_pullGen D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (spMap (dualMap (toF R C)))
      _ (𝟙 _) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [Category.id_comp]
    rw [GlobalTheory.T.generatorValue_linComb_change_of_charts D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (gm₀.3 _)
      (spMap (dualMap (toF R C))) _ (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j))
      (top_le_wchart _ _ _ _ (fun j => by rw [← hφ]; exact hpj j)) (top_le_wchart _ _ _ _ (fun j => hJb _))]
    have hn := norm_natCast_le_one_kummer_theta_logarithms (dualMap (toF R C)) (𝟙 _) (LB.wchart D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) (((gm₀.s (ν.eX α)).s fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)).val)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hJ _))
    rw [Category.comp_id] at hn
    rw [hn, IsUnit.unit_spec]
    unfold TanExp.termV
    simp only [map_mul]
    refine alg_lemma_5 _ _ _ _ _ _ _ ?_
    rw [← Finset.prod_mul_distrib]
    simp only [Category.id_comp, ← hφ]
    rw [Finset.prod_congr rfl (fun j _ => GlobalTheory.T.transitionUnitPowValueAtPoint_cocycle D.P.L D.P.isLB _ _ _ _ _ (hν _) (hpj j) (by rw [hφ]; exact hJb _))]
    simp only [gl_gtφT_famφB]
    have tadd : ∀ (i : Fin 4) (a b : ℤ), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) a * trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i)
        (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i)) (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) b =
        trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) (a + b) :=
      fun i a b => trV_add _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _)) a b
    have tzero : ∀ (i : Fin 4), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) 0 = 1 :=
      fun i => trV_zero _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _))
    rw [Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_prod_four_rearrange, tadd, tadd, tadd, tadd]
    have h0 : D.famφB (ν.eX α) 0 = 𝟙 _ := by
      unfold DegPre.famφB
      rfl
    simp only [sub_add_cancel, add_neg_cancel, neg_add_cancel, tzero, _root_.mul_one, h0, Category.comp_id]

end GlobalTheory.MBLow.TanGauge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.VarFlag

section Tri

variable {ι : Type} {m : ι → ℕ}

theorem par_map {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) {M : Mat m R} (hu : ∀ τ, IsUnit (M τ).det)
    (hl : ∀ τ i k, i < k → M τ i k = 0) : Par m ⊤ (M.map ψ) := fun τ => by
  refine ⟨fun _ _ => trivial, ?_, trivial, fun i j _ hij => ?_⟩
  · show (ψ.mapMatrix (M τ)).det ≠ 0
    rw [← RingHom.map_det]
    exact ((hu τ).map ψ).ne_zero
  · show ψ (M τ i j) = 0
    rw [hl τ i j hij, map_zero]

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem carries_at_image {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} (hc : C.Carries p g) :
    ∃ (φ₀ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))
      (g₀ : EigFrame Z φ₀ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z))
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ),
      g₀.Tri (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t ∧
      g₀.Tri (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g t' := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, h2, h3⟩ := hc
  have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
    have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
      (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
        (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫
          spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hρ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ stalkPt C.Y y =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hx₀ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ (stalkPt C.Y y ≫ C.π ≫ genι Z) =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨g₀, hg₀⟩ := ValCoord.exists_bc f (C.Y.X.presheaf.stalkSpecializes hsp).hom hx₀
  exact ⟨_, g₀, t, t', ValCoord.tri_bc hx₀ hg₀ (by rw [← CarriesAt.algebraMap_eq_comp_specializes hsp]; exact h2),
    ValCoord.tri_bc hx₀ hg₀ (by rw [← hψ]; exact h3)⟩

theorem tri_of_carries {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} {g' : EigFrame Z φ' x}
    (hg : C.Carries p g) (hg' : C.Carries p g') : ∃ t, g.Tri (RingHom.id K) g' t := by
  obtain ⟨φ₀, g₀, t, s, T1, T2⟩ := carries_at_image C hg
  obtain ⟨φ₀', g₀', t₂, s₂, T1', T2'⟩ := carries_at_image C hg'
  have hinj : Function.Injective
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) :=
    IsFractionRing.injective _ _
  obtain rfl : φ₀' = φ₀ := RingHom.ext fun a =>
    hinj ((RingHom.congr_fun T1'.2.1 a).symm.trans (RingHom.congr_fun T1.2.1 a))
  have hφ : φ' = φ := T2'.2.1.trans T2.2.1.symm
  obtain ⟨T, hT, hTd, hTl⟩ := (g₀.tri_iff _ C.f0 t).1 T1
  obtain ⟨T₂, hT₂, hT₂d, hT₂l⟩ := (g₀'.tri_iff _ C.f0 t₂).1 T1'
  obtain ⟨h, hh, hhd, hhl⟩ := (g₀.tri_iff _ g s).1 T2
  obtain ⟨h₂, hh₂, hh₂d, hh₂l⟩ := (g₀'.tri_iff _ g' s₂).1 T2'
  have hS₀ : g₀.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g₀ inferInstance
  have hid : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (RingHom.id _) ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))) = 𝟙 _ from Spec.map_id _,
      Category.id_comp]

  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ (RingHom.id _)
    inferInstance hS₀ hid (RingHom.id_comp _).symm).1 g₀'
  have hMd := hMu M hM

  have hc1 : g₀.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0
      (T₂ * M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ C.f0 (RingHom.id _)
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) M T₂ inferInstance hM hT₂
    rwa [RingHom.comp_id] at this
  have heq := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hT.1 hT.2.1).1
    C.f0).1).unique hT hc1
  have hPT : Par Dw.mult ⊤ T := CarriesAt.par_of_tri (fun τ i => by rw [hTd]; exact Units.ne_zero _) hTl
  have hPT₂ : Par Dw.mult ⊤ T₂ := CarriesAt.par_of_tri (fun τ i => by rw [hT₂d]; exact Units.ne_zero _) hT₂l
  have hPM : Par Dw.mult ⊤
      (M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have e : M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) =
        T₂⁻¹ * T := by
      rw [heq, ← mul_assoc, Mat.inv_mul hPT₂.det_ne, one_mul]
    rw [e]
    exact hPT₂.inv.mul hPT
  have hMl : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hik => by
    have h0 := (hPM τ).2.2.2 i k i.2 hik
    exact hinj (by rw [map_zero]; exact h0)

  have hSg : g.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g inferInstance
  have hidK : x = spMap (RingHom.id K) ≫ x := by
    rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨N, hN, -⟩, -⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g _ φ' _ (RingHom.id K)
    inferInstance hSg hidK (by rw [RingHom.id_comp]; exact hφ)).1 g'
  have c1 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (N * h.map (RingHom.id K)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g _ _ _ g'
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom (RingHom.id K) h N inferInstance hh hN
    rwa [RingHom.id_comp] at this
  have c2 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ g' (RingHom.id _)
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom M h₂ inferInstance hM hh₂
    rwa [RingHom.comp_id] at this
  have heqK := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hh₂.1 hh₂.2.1).1
    g').1).unique c1 c2
  have hmid : h.map (RingHom.id K) = h := funext fun τ => by ext i j; rfl
  rw [hmid] at heqK
  have hPh : Par Dw.mult ⊤ h := CarriesAt.par_of_tri (fun τ i => by rw [hhd]; exact Units.ne_zero _) hhl
  have hPh₂ : Par Dw.mult ⊤ h₂ := CarriesAt.par_of_tri (fun τ i => by rw [hh₂d]; exact Units.ne_zero _) hh₂l
  have hPMK := par_map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom hMd hMl
  have hNe : N = h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom * h⁻¹ := by
    rw [← heqK, mul_assoc, Mat.mul_inv hPh.det_ne, mul_one]
  have hPN : Par Dw.mult ⊤ N := by
    rw [hNe]
    exact (hPh₂.mul hPMK).mul hPh.inv
  exact ⟨fun τ i => Units.mk0 _ (CarriesAt.Par.diag_ne hPN τ i),
    (g.tri_iff _ g' _).2 ⟨N, hN, fun _ _ => rfl, fun τ i k hik => (hPN τ).2.2.2 i k i.2 hik⟩⟩

theorem carriesTri : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)},
    ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C := by
  intro E _ _ _ H Dw l Xo c Y C K _ φ φ' x p g g' hg hg'
  exact tri_of_carries C hg hg'

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem tri_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {S : Type} [CommRing S] {φ : c.F →+* S} (z : Sp S ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') (g g' : EigFrame Y φ (z ≫ π)) (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') : ∃ d, g.Tri (RingHom.id S) g' d := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have h1 : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
  refine ⟨fun τ i => F.TAt k k' z hh (some ⟨τ, i⟩), by rw [h2, Category.id_comp], rfl, fun τ i =>
    ⟨fun j => (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) j i, rfl, fun j hj => F.B_map_tri k k' τ _ hj, ?_⟩⟩
  simp only [h1, Category.id_comp]
  have e : (fun j => g.v τ j) = fun j => (tv (F.vecAt k z hz rfl τ j)).left := funext (hg τ)
  rw [e, hg' τ i, GlobalTheory.LieMet.isComb_iff]
  exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i

end GlobalTheory.VarFlag

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_congr {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x x' : Sp K ⟶ Y.X} (h : x = x') (g : EigFrame Y φ x) (g' : EigFrame Y φ x')
    (hv : ∀ τ i, g.v τ i = g'.v τ i) (p : Sp K ⟶ C.Y.X) : C.Carries p g ↔ C.Carries p g' := by
  subst h
  obtain ⟨v, a1, a2, a3⟩ := g
  obtain ⟨v', b1, b2, b3⟩ := g'
  have e : v = v' := funext fun τ => funext fun i => hv τ i
  subst e
  rfl

theorem carries_of_tri {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {g' : EigFrame Y φ' x'}
    {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (h : g.Tri (RingHom.id K) g' d) {p : Sp K ⟶ C.Y.X}
    (hp : C.Carries p g) : C.Carries p g' := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  exact ⟨y, ψ, φ₁, f, t, _, h1, h2, GlobalTheory.ShFam.FlatSec.tri_trans h3 h⟩

theorem carries_over {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {p : Sp K ⟶ C.Y.X} (hp : C.Carries p g) :
    p ≫ C.π ≫ genι Y = x := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  rw [h1, Category.assoc, ← h3.1]

theorem uniq_rel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ GlobalTheory.Toroidal.gen Y) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ GlobalTheory.Toroidal.genStr Y = spMap χ → ∀ g : GlobalTheory.ShFam.EigFrame Y χ (x ≫ GlobalTheory.Toroidal.genι Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hlifts hbar K _ z
  set zz := z ≫ GlobalTheory.CompHS.inc₀ X Z with hzz

  let φ : c.F →+* K := (Spec.preimage (zz ≫ X.π ≫ Y.s)).hom
  have hφ : zz ≫ X.π ≫ Y.s = spMap φ := (Spec.map_preimage _).symm

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover zz
  obtain ⟨g, hg⟩ := hFE K φ zz k hk hφ

  let xg : Sp K ⟶ gen Y := zz ≫ X.π ≫ inv (genι Y)
  have hxg : xg ≫ genι Y = zz ≫ X.π := by simp [xg]
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hstr : xg ≫ genStr Y = spMap φ := by
    have e : genStr Y = genι Y ≫ Y.s := by
      calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
        _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
    rw [e, ← Category.assoc, hxg, Category.assoc, hφ]

  have hr : Set.range xg ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    refine (hbar _).1 ?_
    have e : genι Y (xg a) = X.π (GlobalTheory.CompHS.inc₀ X Z (z a)) := by
      rw [← Scheme.Hom.comp_apply, hxg]; rfl
    rw [e]
    have hm : GlobalTheory.CompHS.inc₀ X Z (z a) ∈ X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z := by
      have := (Scheme.Opens.range_ι (X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z)).le ⟨z a, rfl⟩
      exact this
    exact hm
  let x' := IsOpenImmersion.lift j xg hr
  have hx' : x' ≫ j = xg := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ (xg ≫ genι Y), ∀ τ i, g0.v τ i = g.v τ i := by
    rw [hxg]; exact ⟨g, fun _ _ => rfl⟩
  obtain ⟨p, ⟨hp1, hp2⟩, hpu⟩ := hlifts K φ xg x' hx' hstr g0
  refine ⟨p, ⟨φ, k, hk, g, hφ, hg, (carries_congr C hxg g0 g hg0 p).1 hp2⟩, ?_⟩
  rintro p' ⟨φ', k', hk', g', hφ', hg', hc'⟩
  have e : φ' = φ := by
    have h0 : spMap φ' = spMap φ := hφ'.symm.trans hφ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst e
  obtain ⟨d, hd⟩ := tri_of_isFrameAt X.F zz k' k hk' hk g' g hg' hg
  have hc : C.Carries p' g := carries_of_tri C hd hc'
  have hc0 : C.Carries p' g0 := (carries_congr C hxg g0 g hg0 p').2 hc
  refine hpu p' ⟨?_, hc0⟩
  have h1 : p' ≫ C.π = xg := by
    rw [← cancel_mono (genι Y), Category.assoc]
    exact carries_over C hc0
  rw [← cancel_mono j, Category.assoc, ← hπ, h1, hx']

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeLogFormAbsLeStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_degree_log_form_abs_le : Size → Covers fun Fm x _ ι p i Y PP _ => |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by
  first | exact @GlobalTheory.CovTop.FlatSz.flatDegVal_covers | exact GlobalTheory.CovTop.FlatSz.flatDegVal_covers | (intros; apply GlobalTheory.CovTop.FlatSz.flatDegVal_covers <;> assumption)
end

