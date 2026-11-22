import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverDescent

theorem eq_of_geometric_points {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rw [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this
  exact this

theorem isReduced_of_smooth_algebra (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] : _root_.IsReduced S := by
  have hs : Smooth (spMap (algebraMap R S)) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 ‹_›)
  have : IsReduced (Sp S) := GlobalTheory.isReduced_of_smooth_of_isReduced (spMap (algebraMap R S))
  exact (affine_isReduced_iff (CommRingCat.of S)).1 this

open scoped TensorProduct in

theorem exists_lift_geometric (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.FaithfullyFlat R S] (k : Type) [Field k] [IsAlgClosed k]
    (χ : R →+* k) : ∃ χ' : S →+* k, χ'.comp (algebraMap R S) = χ := by
  letI : Algebra R k := χ.toAlgebra
  haveI : Nontrivial (k ⊗[R] S) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := inferInstance
  let g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩
  ext x
  have e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
    rfl
  change g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x
  rw [e]
  exact g.commutes (χ x)

open scoped TensorProduct in

theorem exists_preimage_of_geometric (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S] (w : S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ₁ χ₂ : S →+* k),
      χ₁.comp (algebraMap R S) = χ₂.comp (algebraMap R S) → χ₁ w = χ₂ w) :
    ∃ u : R, algebraMap R S u = w := by
  haveI := isReduced_of_smooth_algebra R S
  haveI := isReduced_of_smooth_algebra S (S ⊗[R] S)
  have key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w := by
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    refine h k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_
    ext x
    change χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact (Algebra.IsEffective.of_faithfullyFlat R S w).1 (by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])

theorem exists_affine_lift {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f]
    (R : Type) [CommRing R] (t : Sp R ⟶ X) :
    ∃ (S : Type) (_ : CommRing S) (φ : R →+* S) (t' : Sp S ⟶ Y),
      φ.Finite ∧ φ.Smooth ∧ φ.FaithfullyFlat ∧ t' ≫ f = spMap φ ≫ t := by
  let Z := pullback f t
  let g : Z ⟶ Sp R := pullback.snd f t
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ g)
  have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have h4 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  refine ⟨Γ(Z, ⊤), inferInstance, φ.hom, Z.isoSpec.inv ≫ pullback.fst f t,
    (IsFinite.SpecMap_iff φ).1 h1, (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2, ?_, ?_⟩
  · rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).1 h3, h4.surj⟩
  · change _ = Spec.map φ ≫ t
    rw [hφ, Category.assoc, pullback.condition, Category.assoc]

section Eval
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_of_test (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (f : Rul Xo c) (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F) (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
    (z : FrPt Xo c S) (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have ht : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dif_pos ht]
  exact hWD f hf S _ p _ φ _ y z ht.choose_spec.choose_spec.choose_spec h

theorem evR_baseChange (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hT : AllTest Xo c)
    (f : Rul Xo c) (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [_root_.IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T) (h : FrMap ψ y z) :
    evR Xo c f z = ψ (evR Xo c f y) := by
  obtain ⟨p, φ, y0, h0⟩ := hT S y
  rw [evR_of_test hWD f hf p φ y0 y h0, evR_of_test hWD f hf p (ψ.comp φ) y0 z
    (((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 _ _ _ φ ψ y0 y z h0).1 h)]
  rfl

theorem exists_cover_point {l₂ : Level H} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂} (hc : c.F = c₂.F)
    (r : Xo₂.X ⟶ Xo.X) (rF : Xo₂.XF c₂ ⟶ Xo.XF c)
    (h1 : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h2 : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom)
    [IsFinite rF] [Etale rF] [Surjective rF]
    (R : Type) [CommRing R] [Algebra c.F R] (x : Sp R ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c R) :
    ∃ (S : Type) (_ : CommRing S) (φ : R →+* S) (j : c₂.F →+* S) (x₂ : Sp S ⟶ Xo₂.X),
      φ.Finite ∧ φ.Smooth ∧ φ.FaithfullyFlat ∧
      j.comp (IntermediateField.inclusion hc.le).toRingHom = φ.comp (algebraMap c.F R) ∧
      x₂ ≫ r = spMap φ ≫ x ∧
      x₂ ≫ Xo₂.s = spMap (j.comp (IntermediateField.inclusion c₂.le).toRingHom) := by
  let t : Sp R ⟶ Xo.XF c := pullback.lift x (spMap (algebraMap c.F R)) (by
    rw [hx, sOf, ← Spec.map_comp]; rfl)
  obtain ⟨S, _, φ, t', f1, f2, f3, ht⟩ := exists_affine_lift rF R t
  obtain ⟨j, hj⟩ := Spec.map_surjective (R := CommRingCat.of c₂.F) (S := CommRingCat.of S)
    (t' ≫ pullback.snd _ _)
  refine ⟨S, inferInstance, φ, j.hom, t' ≫ pullback.fst _ _, f1, f2, f3, ?_, ?_, ?_⟩
  · have e : Spec.map j ≫ spMap (IntermediateField.inclusion hc.le).toRingHom =
        spMap φ ≫ spMap (algebraMap c.F R) := by
      rw [hj, Category.assoc, ← h2, ← Category.assoc, ht, Category.assoc, pullback.lift_snd]
    rw [← Spec.map_comp, ← Spec.map_comp] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  · rw [Category.assoc, ← h1, ← Category.assoc, ht, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ← hj, ← Spec.map_comp]
    rfl

end Eval

theorem shortValue_descends : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), EvalWD (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) → AllTest d.Xo₂ d.c₂ → @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃! u : p.R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (χ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z → ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v → χ u = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
  intro hL hC E _ _ _ H Dw l Xo c n d hWD hAT hN hlev hA _ hnab hph Λ N hU hTr hLv a P hP x0 β p y
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hTr hLv a P hP
    (d.w x0) β
  have hinv := GlobalTheory.T.cover_mul_shortThetaSeries_indep_of_framed_lift hL hC E H Dw l Xo c n d hN hlev hA hnab hph Λ N hU hTr hLv a P hP x0 β
  have hbc := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c
  have hbc₂ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂
  have hcomp := (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1
  obtain ⟨hdvd, hM, -, -, -, -, hlift, hsec, -⟩ := id hlev
  obtain ⟨r, jK, m, -, -, he, heA, -, hF⟩ := hN l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h1, h2, _, _, _, -⟩ := hF c d.c₂ d.hF.symm
  have hEta : DeltaDat.EtaOK { d with r := r, m := m } := by
    refine ⟨fun b => ?_, heA⟩
    have := he b
    rwa [hM, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)] at this
  obtain ⟨hov1, hov2, -⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n { d with r := r, m := m }
  obtain ⟨S, _, φ, j, x₂, f1, f2, f3, hj, hx, hx'⟩ :=
    exists_cover_point d.hF.symm r rF h1 h2 p.R y.x y.x_over
  letI : Algebra p.R S := φ.toAlgebra
  letI : Algebra c.F S := (φ.comp (algebraMap c.F p.R)).toAlgebra
  letI : Algebra d.c₂.F S := j.toAlgebra
  haveI : Module.Finite p.R S := f1
  haveI : Algebra.Smooth p.R S := f2
  haveI : Module.FaithfullyFlat p.R S := f3
  haveI := isReduced_of_smooth_algebra p.R S
  have hS : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := fun a =>
    RingHom.congr_fun hj a
  let φa : p.R →ₐ[c.F] S := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := hbc p.R S φa y
  obtain ⟨y₂, -, hy₂⟩ := hov1 S hS y' x₂ (hx.trans hy'.1.symm) hx'
  obtain ⟨v₀, hv₀, -⟩ := hval S y₂
  have core : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (χ' : S →+* k), χ'.comp φ = χ.toRingHom →
      ∀ (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
      ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v →
        χ' (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
    intro k _ _ _ _ hk χ χ' hχ z z₂ hz hz₂ v hv
    have c1 : ∀ a : c.F, χ' (algebraMap c.F S a) = algebraMap c.F k a := fun a =>
      (RingHom.congr_fun hχ (algebraMap c.F p.R a)).trans (χ.commutes a)
    let ψ : S →ₐ[c.F] k := { χ' with commutes' := c1 }
    let ψ₂ : S →ₐ[d.c₂.F] k := { χ' with
      commutes' := fun b => by
        obtain ⟨a, rfl⟩ := d.eF.surjective b
        exact (congrArg χ' (hS a)).trans ((c1 a).trans (hk a).symm) }
    have hψ : ψ.comp φa = χ := AlgHom.ext fun x => RingHom.congr_fun hχ x
    have hz' : FrMap ψ y' z := (hcomp _ _ _ φa ψ y y' z hy').2 (by rw [hψ]; exact hz)
    obtain ⟨w₂, hw₂⟩ := hbc₂ S k ψ₂ y₂
    have hw := hov2 S hS k hk ψ ψ₂ rfl y' y₂ z w₂ hy₂ hz' hw₂
    obtain ⟨v', hv', -⟩ := hval k w₂
    rw [hinv r m hEta k hk z z₂ w₂ hz₂ hw v v' hv hv', ← hnat S k ψ₂ y₂ w₂ hw₂ v₀ v' hv₀ hv',
      evR_baseChange hWD hAT d.cδ hsec.1 ψ₂ y₂ w₂ hw₂]
    exact map_mul χ' _ _
  have pts : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : p.R →+* k),
      ∃ (_ : Algebra c.F k) (_ : Algebra d.c₂.F k) (χa : p.R →ₐ[c.F] k) (z : FrPt Xo c k)
        (z₂ : FrPt d.Xo₂ d.c₂ k) (v : k),
        (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) ∧ χa.toRingHom = χ ∧
        FrMap χa y z ∧ FrOver d z₂ z ∧ ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v := by
    intro k _ _ χ
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    letI i2 : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
      congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hbc p.R k χa y
    obtain ⟨z₂, hz₂⟩ := hlift k hk z
    obtain ⟨v, hv, -⟩ := hval k z₂
    exact ⟨i1, i2, χa, z, z₂, v, hk, rfl, hz, hz₂, hv⟩
  obtain ⟨u, hu⟩ := exists_preimage_of_geometric p.R S (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) (by
    intro k _ _ χ₁ χ₂ h12
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k (χ₁.comp φ)
    exact (core k hk χa χ₁ hχ.symm z z₂ hz hz₂ v hv).trans
      (core k hk χa χ₂ (h12.symm.trans hχ.symm) z z₂ hz hz₂ v hv).symm)
  refine ExistsUnique.intro u ?_ ?_
  · intro k _ _ _ _ hk χ z z₂ hz hz₂ v hv
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ.toRingHom
    rw [← core k hk χ χ' hχ' z z₂ hz hz₂ v hv, ← hu]
    exact (RingHom.congr_fun hχ' u).symm
  · intro u' hu'
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k χ
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ
    subst hχ
    have e := core k hk χa χ' hχ' z z₂ hz hz₂ v hv
    rw [← hu] at e
    exact (hu' k hk χa z z₂ hz hz₂ v hv).trans (e.symm.trans (RingHom.congr_fun hχ' u))

end GlobalTheory.CoverDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAuxiliaryWeightsAtRunWeights
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.AuxiliaryWeightsExistence

theorem antitone_nonneg_of_gaps {p : ℕ} (g : Fin p → ℤ)
    (hg : ∀ (i : Fin p) (h : i.1 + 1 < p), g ⟨i.1 + 1, h⟩ ≤ g i)
    (hl : ∀ i : Fin p, i.1 + 1 = p → 0 ≤ g i) : Antitone g ∧ ∀ i, 0 ≤ g i := by

  have walk : ∀ k : ℕ, ∀ i j : Fin p, j.1 = i.1 + k → g j ≤ g i := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have : j = i := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro i j hij
      have hm : i.1 + k < p := by have := j.2; omega
      have hstep := hg ⟨i.1 + k, hm⟩ (by have := j.2; simp only; omega)
      have hj : (⟨i.1 + k + 1, by have := j.2; omega⟩ : Fin p) = j := Fin.ext (by simp only; omega)
      rw [hj] at hstep
      exact le_trans hstep (ih i ⟨i.1 + k, hm⟩ rfl)
  refine ⟨fun i j hij => walk (j.1 - i.1) i j (by have : i.1 ≤ j.1 := hij; omega), fun i => ?_⟩
  have hp : p - 1 < p := by have := i.2; omega
  exact le_trans (hl ⟨p - 1, hp⟩ (by simp only; have := i.2; omega))
    (walk (p - 1 - i.1) i ⟨p - 1, hp⟩ (by simp only; have := i.2; omega))

theorem gap_key (c cL T' r : ℤ) (hT : 0 < T') (hr : 0 ≤ r) (hc : T' * (T' + 2 * r) ≤ c + 2)
    (hL : cL = Int.fdiv (c + 2) T') : c ≤ (T' + 2) * cL := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hT.le] at hL
  have hdm := Int.mul_ediv_add_emod (c + 2) T'
  have hlt := Int.emod_lt_of_pos (c + 2) hT
  have hge := Int.emod_nonneg (c + 2) hT.ne'
  rw [← hL] at hdm

  have hq : T' + 2 * r ≤ cL := by
    by_contra hcon
    rw [not_le] at hcon
    have : T' * (cL + 1) ≤ T' * (T' + 2 * r) := by
      apply mul_le_mul_of_nonneg_left _ hT.le; omega
    nlinarith
  nlinarith

theorem exists_block {p : ℕ} (a l f : Fin p → ℕ) (T Dm r T' : ℕ) (hT' : T' = T + Dm + 2)
    (hf : ∀ i, (f i : ℤ) = a i - T * l i)
    (hgap : ∀ i : Fin p, i.1 + 1 < p → ((T' * (T' + 2 * r) : ℕ) : ℤ) ≤ gapZ a i + 2)
    (hL : ∀ i : Fin p, i.1 + 1 < p → gapZ l i = Int.fdiv (gapZ a i + 2) T')
    (hlast : ∀ i : Fin p, i.1 + 1 = p → (a i : ℤ) ≤ ((T : ℤ) + Dm + 4) * l i) :
    ∃ w : Fin p → ℕ, Antitone w ∧ ∀ i, w i + f i = (Dm + 4) * l i := by

  have hT'z : (T' : ℤ) = T + Dm + 2 := by rw [hT']; push_cast; ring
  have hg := antitone_nonneg_of_gaps (fun i => ((T : ℤ) + Dm + 4) * l i - a i) ?_ ?_
  · refine ⟨fun i => (((T : ℤ) + Dm + 4) * l i - a i).toNat,
      fun i j hij => Int.toNat_le_toNat (hg.1 hij), fun i => ?_⟩
    have h0 := hg.2 i
    have hfi := hf i
    dsimp only at h0 ⊢
    zify
    rw [Int.toNat_of_nonneg h0]
    linarith
  · intro i h
    have hk := gap_key (gapZ a i) (gapZ l i) T' r (by omega) (by positivity)
      (by exact_mod_cast hgap i h) (hL i h)
    unfold gapZ at hk
    rw [dif_pos h, dif_pos h, hT'z] at hk
    nlinarith
  · intro i h
    have := hlast i h
    linarith

private theorem le_mul_fdiv_sub_of_sq_le (a c T Dm : ℤ) (hD : 0 ≤ Dm) (h40 : 40 * (Dm + 2) ≤ T)
    (hc : c ≤ T) (ha : 2 * T ^ 2 ≤ a) :
    a ≤ (T + Dm + 4) * Int.fdiv (a - c) (T + Dm + 2) := by
  have hT : 0 < T + Dm + 2 := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hT.le]
  have hdm := Int.mul_ediv_add_emod (a - c) (T + Dm + 2)
  have hlt := Int.emod_lt_of_pos (a - c) hT
  have hge := Int.emod_nonneg (a - c) hT.ne'
  set q := (a - c) / (T + Dm + 2) with hq
  set m := (a - c) % (T + Dm + 2) with hm

  have h2q : c + T + Dm + 2 ≤ 2 * q := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (T + Dm + 2) * (2 * q) ≤ (T + Dm + 2) * (2 * T + Dm + 1) := by
      apply mul_le_mul_of_nonneg_left _ hT.le
      omega
    have hT0 : (0 : ℤ) ≤ T := by omega
    nlinarith [mul_le_mul_of_nonneg_right h40 hT0, mul_le_mul_of_nonneg_right h40 hD,
      mul_nonneg hD hT0, mul_nonneg hD hD]
  nlinarith

theorem exists_auxiliaryWeights_at_runWeights : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 →
      (∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2) ∧ ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, hgP, hgM, hh0, -, hlP, hlM, -, hnP, -, hPW, -, -, -, hL, hF, -, -, -, h40, hcT, h40W,
    -, -, -, -⟩ := hS
  obtain ⟨hLn, hLP, hLM⟩ := hL
  obtain ⟨hFn, hFP, hFM⟩ := hF
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = Tn + WeightFamilies.dimY D j + 2 := by unfold Tp; push_cast; ring
  have h40z : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40

  have hbigP : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      2 * (Tn : ℤ) ^ 2 ≤ ka.aP τ i := by
    intro τ i hi
    have h1 := hlP τ i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ ka.aP τ i := by linarith
    exact_mod_cast h2
  have hbigM : ∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
      2 * (Tn : ℤ) ^ 2 ≤ ka.aM τ i := by
    intro τ i hi
    have h1 := hlM τ i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ ka.aM τ i := by linarith
    exact_mod_cast h2

  have blockP : ∀ τ, ∃ w : Fin (D.R.sigW j).1 → ℕ, Antitone w ∧
      ∀ i, w i + wF.aP τ i = (WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ
    refine exists_block (ka.aP τ) (wL.aP τ) (wF.aP τ) Tn (WeightFamilies.dimY D j) D.R.r (Tp D j Tn) rfl
      (hFP τ) (hgP τ) ?_ ?_
    · intro i hi
      have hl := hLP τ i
      rw [if_pos hi] at hl
      exact hl
    · intro i hi
      have hn : ¬ (i.1 + 1 < (D.R.sigW j).1) := by omega
      have hl := hLP τ i
      rw [if_neg hn] at hl
      unfold gapZ at hl
      rw [dif_neg hn] at hl
      have hk := le_mul_fdiv_sub_of_sq_le (ka.aP τ i) (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) Tn
        (WeightFamilies.dimY D j) (by positivity) h40z (by exact_mod_cast hcT) (hbigP τ i hi)
      have e : (ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r =
          ka.aP τ i - (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) := by ring
      rw [hl, e, hTp]
      exact hk
  have blockM : ∀ τ, ∃ w : Fin (D.R.sigW j).2 → ℕ, Antitone w ∧
      ∀ i, w i + wF.aM τ i = (WeightFamilies.dimY D j + 4) * wL.aM τ i := by
    intro τ
    refine exists_block (ka.aM τ) (wL.aM τ) (wF.aM τ) Tn (WeightFamilies.dimY D j) D.R.r (Tp D j Tn) rfl
      (hFM τ) (hgM τ) ?_ ?_
    · intro i hi
      have hl := hLM τ i
      rw [if_pos hi] at hl
      exact hl
    · intro i hi
      have hn : ¬ (i.1 + 1 < (D.R.sigW j).2) := by omega
      have hl := hLM τ i
      rw [if_neg hn] at hl
      unfold gapZ at hl
      rw [dif_neg hn] at hl
      have hk := le_mul_fdiv_sub_of_sq_le (ka.aM τ i) 0 Tn (WeightFamilies.dimY D j) (by positivity) h40z
        (by positivity) (hbigM τ i hi)
      rw [sub_zero] at hk
      rw [hl, hTp]
      exact hk
  choose bP hbPa hbPs using blockP
  choose bM hbMa hbMs using blockM
  have hnW : Even nW := hLn ▸ wL.n_even
  have hle : nP ≤ (WeightFamilies.dimY D j + 4) * nW := le_trans hPW (by nlinarith)
  have hn2 : Even ((WeightFamilies.dimY D j + 4) * nW - nP) :=
    (Nat.even_sub hle).2 ⟨fun _ => hnP, fun _ => hnW.mul_left _⟩
  have hP2 : ∀ τ, Antitone (fun i => 2 * wL.aP τ i) := fun τ a b h => by
    have := wL.aPlus_antitone τ h
    dsimp only
    omega
  have hM2 : ∀ τ, Antitone (fun i => 2 * wL.aM τ i) := fun τ a b h => by
    have := wL.aM_anti τ h
    dsimp only
    omega
  have hn1 : Even (2 * nW - 2) := ⟨nW - 1, by omega⟩
  refine ⟨⟨(⟨bP, bM, hbPa, hbMa, (WeightFamilies.dimY D j + 4) * nW - nP, hn2⟩ : WeightFamilies.Wt D j), ?_, hbPs, hbMs⟩,
    ⟨(⟨fun τ i => 2 * wL.aP τ i, fun τ i => 2 * wL.aM τ i, hP2, hM2, 2 * nW - 2, hn1⟩ : WeightFamilies.Wt D j),
      ?_, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · show (WeightFamilies.dimY D j + 4) * nW - nP + wF.n = (WeightFamilies.dimY D j + 4) * wL.n
    rw [hFn, hLn]
    exact Nat.sub_add_cancel hle
  · show 2 * nW - 2 + 2 = 2 * nW
    omega

end GlobalTheory.AuxiliaryWeightsExistence
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.H2XNIffH2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) (X : PJ D B P j) (E : PtExt X)
  (hM : IntAtExt X E)

abbrev xN : PJ D n.base P j := PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)

def globalFamilyDataBaseChange {ka wL wF : WeightFamilies.Wt D j} (G : EtaleWeightGaps.GlobalFamilyData X ka wL wF) : EtaleWeightGaps.GlobalFamilyData (xN n X E hM) ka wL wF where
  N := G.N
  w := G.w
  del := G.del
  th' := G.th'
  rz := G.rz
  alz := G.alz
  th0 := G.th0
  zc := G.zc
  rq := G.rq
  th := G.th
  iet := G.iet
  et := G.et
  mx := G.mx

end General

end GlobalTheory.RunIn
end
end

