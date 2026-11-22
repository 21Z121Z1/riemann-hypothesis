import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3271
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPairStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_endomorphisms_adjoint_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  first | exact @GlobalTheory.Mum.linEnd_adjoint_lbIso | exact GlobalTheory.Mum.linEnd_adjoint_lbIso | (intros; apply GlobalTheory.Mum.linEnd_adjoint_lbIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointExtendsAlongThetaMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtP

theorem genericFibre_polAV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)), GenOf Xo c y t → ∃ (P : PolAV (Sp (FractionRing R))) (α : P.A.left ⟶ Xo.univ.t.G.left) (α' : P.A.left ⟶ t.G.left), P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ IsGrpPullback P.A Xo.univ.t.G (y ≫ pullback.fst _ _) α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsGrpPullback P.A t.G (jK R) α' ∧ LBIso P.L (t.PP.L.pull α') := by
  intro E _ _ _ H Dw l Xo c R _ _ y t hy
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  have hw₁ : LBIso tK.PP.L (t.PP.L.pull m₁.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₁.lin; exact ⟨w, hw⟩
  have hw₂ : LBIso tK.PP.L (Xo.univ.t.PP.L.pull m₂.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₂.lin; exact ⟨w, hw⟩
  have hd := GlobalTheory.UMin.polFib_univ E H Dw l Xo c (FractionRing R) (𝟙 _ ≫ y ≫ pullback.fst _ _)
  obtain ⟨P, α₀, hgP, hpb₀, hL₀⟩ := ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ Xo.univ.t.G Xo.univ.t.PP.L tK.G tK.PP.L
    (y ≫ pullback.fst _ _) m₂.cm.F Xo.univ.t.PP.isLB tK.PP.isLB m₂.cart hw₂ _ (FractionRing R) (𝟙 _)).1).2 hd
  refine ⟨P, α₀ ≫ m₂.cm.F, α₀ ≫ m₁.cm.F, hgP, ?_, ?_, ?_, ?_⟩
  · have h := hpb₀.comp m₂.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB Xo.univ.t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₂ α₀ rfl)
  · have h := hpb₀.comp m₁.cart
    rwa [Category.id_comp] at h
  · exact LBIso.trans P.isLB (pull_isLB tK.PP.isLB α₀) (pull_isLB t.PP.isLB _) hL₀
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hw₁ α₀ rfl)

theorem extend_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ b : o →+* c.F, f ≫ PSpace.str o n = pullback.snd _ _ ≫ spMap b → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t → ∀ σ : Sp R ⟶ Sp o, jK R ≫ σ = y ≫ pullback.snd _ _ ≫ spMap b → ∃ ξ : Sp R ⟶ PSpace o n, jK R ≫ ξ = y ≫ f ∧ ξ ≫ PSpace.str o n = σ := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm h3 hmu hn hTh b hb R _ _ _ hR t hP y hy σ hσ
  haveI : IsNoetherianRing R := hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgdef
  obtain ⟨σ₀, hnz⟩ := GlobalTheory.T.exists_polarisation_section_nonvanishing_closed_fibre E H R hR t hP
  obtain ⟨P, α, α', hg, hpb, hL, hpb', hL'⟩ := genericFibre_polAV E H Dw l Xo c R y t hy
  have hpb₁ : IsGrpPullback P.A t.G (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) α' := by
    rw [Category.comp_id]; exact hpb'
  have hpf : PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) := ⟨P, α', hg, hpb₁, hL'⟩
  let θ := SecAt.pull t.G t.PP.L σ₀ (algebraMap R (FractionRing R))
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R)
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) θ hm hn hpf
  let β : o →+* R := (Spec.preimage σ).hom
  have hβ : spMap β = σ := Spec.map_preimage σ
  have hmR : IsUnit (m : R) := by simpa [β] using hmu.map β
  obtain ⟨e', he', j, hj⟩ := GlobalTheory.T.thetaSymmetricFunctions_integral_unit_normalLocalDomain E H (Sp R) t g m (n + 1) R (𝟙 _) σ₀ e hm h3 hmR hn hpf hnz he
  have hne : ∃ j, e j ≠ 0 := ⟨j, fun h0 => hj.ne_zero (IsFractionRing.injective R (FractionRing R)
    ((he' j).trans (h0.trans (map_zero _).symm)))⟩
  have hgen := GlobalTheory.T.generates_sections_of_thetaSymmetricFunctions_ne_zero (Sp R) t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (n + 1) (FractionRing R) _ θ e hm hn hpf he hne
  have hcrd : PCrd (y ≫ f) e := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m n o (Xo.XF c) (pullback.fst _ _) f (Sp R) t.G t.PP.L t.PP.rig (FractionRing R) y
    (spMap (algebraMap R (FractionRing R)) ≫ 𝟙 (Sp R)) P α α' θ e hm hn hTh t.PP.isLB t.PP.rigGen hg hpb hL hpb₁ hL'
    hgen he
  obtain ⟨ξ, hξ1, hξ2⟩ := GlobalTheory.T.exists_projectiveSpace_point_of_unit_coordinate o R n β e' ⟨j, hj⟩
  refine ⟨ξ, ?_, hξ1.trans hβ⟩
  have hc1 : PCrd (jK R ≫ ξ) e := by
    have := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).1 o R (FractionRing R) n ξ e' (algebraMap R (FractionRing R)) hξ2
    have ee : (fun j => algebraMap R (FractionRing R) (e' j)) = e := funext he'
    rw [ee] at this; exact this
  refine (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).1 o (FractionRing R) n (jK R ≫ ξ) (y ≫ f) e ?_ hc1 hcrd
  rw [Category.assoc, hξ1, hβ, Category.assoc, hb]; exact hσ

end GlobalTheory.UMin.ExtP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralChernCombination
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm.PolarSum

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x
  simp only [evalF, fld, map_add, Pi.add_apply, Subalgebra.coe_add]

theorem evalF_smul {ι : Type} (w : ι → A.Pt → Ev n) (t : ℝ) (P : MvPolynomial ι ℝ) :
    evalF A w (t • P) = (t : ℂ) • evalF A w P := by
  funext x
  simp only [evalF, fld, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C,
    Pi.smul_apply, ← Algebra.smul_def, Subalgebra.coe_smul]
  rfl

theorem re_dens_loc_smul (t : ℝ) (α : A.Fld) (i : A.ι) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    (dens (A.loc ((t : ℂ) • α) i v)).re = t * (dens (A.loc α i v)).re := by
  have h : A.loc ((t : ℂ) • α) i v = (t : ℂ) • A.loc α i v := by
    unfold HolAtlas.loc; split_ifs
    · rfl
    · exact (smul_zero _).symm
  rw [h, ← Complex.re_ofReal_mul]
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

variable [MeasurableSpace M] [BorelSpace M]

theorem part_smul (t : ℝ) (α : A.Fld) (ε ε' : ℤˣ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal c • A.part α ε' := by
  have := ChernScale.glueMeas_restrict_eq A.e
    (ρ := fun i y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc ((t : ℂ) • α) i (A.e i y))).re))
    (ρ' := fun i y => ENNReal.ofReal ((ε' : ℤ) * (dens (A.loc α i (A.e i y))).re))
    (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top MeasurableSet.univ
    (fun i y _ _ => by beta_reduce; rw [re_dens_loc_smul, h, ENNReal.ofReal_mul hc])
  rw [Measure.restrict_univ, Measure.restrict_univ] at this
  exact this

theorem integrable_part_smul {g : M → ℝ} (t : ℝ) {α : A.Fld} (h : ∀ ε : ℤˣ, Integrable g (A.part α ε)) (ε : ℤˣ) :
    Integrable g (A.part ((t : ℂ) • α) ε) := by
  rcases le_total 0 t with ht | ht
  · rw [part_smul A t α ε ε t ht fun x => by ring]
    exact (h ε).smul_measure ENNReal.ofReal_ne_top
  · rw [part_smul A t α ε (-ε) (-t) (neg_nonneg.2 ht) fun x => by rw [Units.val_neg, Int.cast_neg]; ring]
    exact (h _).smul_measure ENNReal.ofReal_ne_top

theorem part_zero_smul (α : A.Fld) (ε : ℤˣ) : A.part (((0 : ℝ) : ℂ) • α) ε = 0 := by
  rw [part_smul A 0 α ε ε 0 le_rfl fun x => by ring, ENNReal.ofReal_zero, zero_smul]

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

theorem wInt_evalF_sum {ι κ : Type} (w : ι → A.Pt → Ev n) (hw : ∀ i, A.IsForm (fld A (w i))) (g : M → ℝ)
    (P : κ → MvPolynomial ι ℝ) (c : κ → ℝ) (s : Finset κ)
    (h : ∀ a ∈ s, ∀ ε : ℤˣ, Integrable g (A.part (evalF A w (P a)) ε)) :
    (∀ ε : ℤˣ, Integrable g (A.part (evalF A w (∑ a ∈ s, c a • P a)) ε)) ∧
      wInt A g (evalF A w (∑ a ∈ s, c a • P a)) = ∑ a ∈ s, c a * wInt A g (evalF A w (P a)) := by
  have hF : ∀ Q, A.IsForm (evalF A w Q) := fun Q => ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.1 ι w Q hw).1
  obtain ⟨-, hadd, hsm, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  induction s using Finset.induction_on with
  | empty =>
    have e : evalF A w 0 = ((0 : ℝ) : ℂ) • evalF A w 0 := by rw [← evalF_smul, zero_smul]
    simp only [Finset.sum_empty]
    rw [e]
    refine ⟨fun ε => ?_, ?_⟩
    · rw [part_zero_smul]; exact integrable_zero_measure
    · rw [hsm g 0 _ (hF _), zero_mul]
  | insert a s ha ih =>
    obtain ⟨i₁, i₂⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    have j₁ : ∀ ε : ℤˣ, Integrable g (A.part (evalF A w (c a • P a)) ε) := by
      rw [evalF_smul]
      exact integrable_part_smul A (c a) (h a (Finset.mem_insert_self a s))
    obtain ⟨k₁, k₂⟩ := hadd g _ _ (hF _) (hF _) j₁ i₁
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evalF_add]
    refine ⟨k₁, ?_⟩
    rw [k₂, i₂, evalF_smul, hsm g _ _ (hF _)]

end Manifold

theorem wInt_sum_lin_pow : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := by
  intro k _ X p D hX σ ι _ L g s c h
  haveI := hX.toIsArithVar.isIntegral
  obtain ⟨h₁, h₂, h₃⟩ := (GlobalTheory.IsArithVar.finite_emb_and_topology hX.toIsArithVar).2 σ
  exact (wInt_evalF_sum (hX.atlas σ) (fun i => c1F hX σ (L i))
    (fun i => ((GlobalTheory.T.firstChern_form_properties k X p D hX σ).1 (L i) (L i)).1.1) g
    (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ D) c s h).2

end GlobalTheory.LineForm.PolarSum
end

