import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapField
section
open Matrix

namespace GlobalTheory.IdemRankLocal

theorem exists_conj_diag (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ)
    (p : Matrix (Fin n) (Fin n) W) (hp : p * p = p) :
    ∃ (r : ℕ) (P P' : Matrix (Fin n) (Fin n) W), P * P' = 1 ∧
    p = P * Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) * P' := by
  classical
  set f : (Fin n → W) →ₗ[W] (Fin n → W) := Matrix.toLin' p with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.toLin'_mul, hp]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  haveI : Module.Projective W (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc x)
  haveI : Module.Projective W (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm x)
  haveI : Module.Finite W (LinearMap.range f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Finite W (LinearMap.ker f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (Submodule.linearProjOfIsCompl_surjective hc.symm)
  haveI : Module.Free W (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free W (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank W (LinearMap.range f)
  set s := Module.finrank W (LinearMap.ker f)
  let b1 := Module.finBasis W (LinearMap.range f)
  let b2 := Module.finBasis W (LinearMap.ker f)
  let bs : Module.Basis (Fin r ⊕ Fin s) W (Fin n → W) :=
    (b1.prod b2).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hrs : r + s = n := by
    have := Module.finrank_eq_card_basis bs
    simpa [Fintype.card_sum] using this.symm
  have hbs1 : ∀ i, f (bs (Sum.inl i)) = bs (Sum.inl i) := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
    obtain ⟨y, hy⟩ := (b1 i).2
    rw [← hy]
    exact LinearMap.congr_fun hf y
  have hbs2 : ∀ i, f (bs (Sum.inr i)) = 0 := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
  let b : Module.Basis (Fin n) W (Fin n → W) := bs.reindex (finSumFinEquiv.trans (finCongr hrs))
  have hb : ∀ j : Fin n, f (b j) = (if j.val < r then (1 : W) else 0) • b j := by
    intro j
    have hj : b j = bs ((finSumFinEquiv.trans (finCongr hrs)).symm j) := Module.Basis.reindex_apply _ _ _
    rw [hj]
    by_cases h : j.val < r
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inl ⟨j, h⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp
      rw [this, if_pos h, one_smul, hbs1]
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inr ⟨j.val - r, by omega⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp; omega
      rw [this, if_neg h, zero_smul, hbs2]
  have hdiag : LinearMap.toMatrix b b f = Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, b.repr_self]
    by_cases hij : i = j
    · subst hij; simp; split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_apply, Ne.symm hij]
      split_ifs <;> simp [Finsupp.single_apply, Ne.symm hij]
  let e := Pi.basisFun W (Fin n)
  refine ⟨r, e.toMatrix b, b.toMatrix e, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  · have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
    rw [← hdiag, this, LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']

theorem rank_map_const : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W),
    Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  intro W _ _ n Q hQ
  classical
  obtain ⟨r, P, P', hPP', hQeq⟩ := exists_conj_diag W n Q hQ
  refine ⟨Fintype.card {i : Fin n // i.val < r}, fun k _ β => ?_⟩
  have hm : P.map β * P'.map β = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ β.map_zero β.map_one]
  have hP : IsUnit (P.map β).det := Matrix.isUnit_det_of_right_inverse hm
  have hP' : IsUnit (P'.map β).det := Matrix.isUnit_det_of_left_inverse hm
  rw [hQeq, Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP, Matrix.diagonal_map β.map_zero,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by split_ifs with h <;> simp [h]))

end GlobalTheory.IdemRankLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemes
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActPull

theorem exists_act_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G' ⟶ G'), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G' ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := by
  intro S S' f G _ G' _ φ hg O _ act hhom hone hmul hadd
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act' : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (φ ≫ (act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act' a) = pushPt hg.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨act', ⟨fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩, ha⟩
  · have := hhom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act' 1), pa, hone, Category.comp_id]
  · rw [← Category.id_comp (act' (a * b)), pa, pa, hmul, ← Category.id_comp (act' a), pa, Category.assoc]
  · refine Eq.trans ?_ (pm (act' a) (act' b)).symm
    rw [← Category.id_comp (act' (a + b)), ← Category.id_comp (act' a), ← Category.id_comp (act' b), pa, pa, pa, hadd]
    exact MonObj.comp_mul _ _ _

end GlobalTheory.ActPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetChar

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

section Alg

variable {R : Type} [CommRing R]

def cut (a : R) (ha : a * a = a) : Rˣ →* Rˣ where
  toFun u := ⟨a * u + (1 - a), a * (u⁻¹ : Rˣ) + (1 - a),
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv,
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv⟩
  map_one' := Units.ext (by simp)
  map_mul' u w := Units.ext (by
    show a * ((u : R) * w) + (1 - a) = (a * u + (1 - a)) * (a * w + (1 - a))
    linear_combination (-((u : R) * w) + u + w - 1) * ha)

theorem cut_val (a : R) (ha : a * a = a) (u : Rˣ) : (cut a ha u : R) = a * u + (1 - a) := rfl

theorem continuous_cut [TopologicalSpace R] [IsTopologicalRing R] (a : R) (ha : a * a = a) :
    Continuous (cut a ha) :=
  Units.continuous_iff.2 ⟨(continuous_const.mul Units.continuous_val).add continuous_const,
    (continuous_const.mul Units.continuous_coe_inv).add continuous_const⟩

theorem mul_det {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, a * (M - 1) i j = 0) :
    a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R a)
  have hI : ∀ x, x ∈ I ↔ x * a = 0 := fun x => Iff.rfl
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 ((mul_comm _ _).trans (h i j)))
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, det_one, map_one]
  have h3 := (hI _).1 (Ideal.Quotient.eq.1 h2)
  linear_combination h3

end Alg

theorem eq_single {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε = pl D v := by
  obtain ⟨α, rfl, h3, h4⟩ := h
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_glue (D : D7) (e : HeightOneSpectrum (𝓞 D.host.F) → Formalism.L2.Theta.AE D)
    (hee : ∀ v, e v * e v = e v) (hp : ∀ v, e v * pl D v = e v) :
    ∃ a : Formalism.L2.Theta.AE D, a * a = a ∧ infPart D a = 0 ∧ ∀ v, a * pl D v = e v := by
  obtain ⟨ι, -, -, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h1 : ∀ v (Q : HeightOneSpectrum (𝓞 D.host.E)), Q.under (𝓞 D.host.F) = v →
      ι (finPart D (pl D v)) Q = 1 := fun v Q hQ => by
    refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_)
    have := happ (singleV D.host.F v 1) 1 Q n (by
      rw [map_one, hQ, GlobalTheory.PlaceIdem.single_same, sub_self, map_zero]
      exact zero_le)
    rwa [map_one, map_one] at this
  have h0 : ∀ v (Q : HeightOneSpectrum (𝓞 D.host.E)), Q.under (𝓞 D.host.F) ≠ v →
      ι (finPart D (pl D v)) Q = 0 := fun v Q hQ => by
    refine GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_
    have := happ (singleV D.host.F v 1) 0 Q n (by
      rw [map_zero, GlobalTheory.PlaceIdem.single_ne hQ, sub_self, map_zero]
      exact zero_le)
    rwa [map_zero, map_zero, sub_zero] at this
  have hinf : ∀ v, infPart D (pl D v) = 0 := fun v => TensorProduct.zero_tmul _ _
  let f : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.adicCompletion D.host.E :=
    fun Q => ι (finPart D (e (Q.under (𝓞 D.host.F)))) Q
  have hff : ∀ Q, f Q * f Q = f Q := fun Q => by
    simp only [f]
    rw [← GlobalTheory.PlaceIdem.mul_ap, ← map_mul, ← RingHom.map_mul, hee]
  have hint : ∀ Q, f Q ∈ Q.adicCompletionIntegers D.host.E := fun Q => by
    by_cases h : f Q = 0
    · rw [h]; exact zero_mem _
    · rw [mul_left_cancel₀ h ((hff Q).trans (mul_one _).symm)]; exact one_mem _
  let b : FiniteAdeleRing (𝓞 D.host.E) D.host.E := ⟨f, Filter.Eventually.of_forall hint⟩
  have hb : ∀ Q, b Q = f Q := fun _ => rfl
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.PlaceIdem.parts_surj D 0 (ι.symm b)
  have ha3 : ι (finPart D a) = b := by rw [ha2, ι.apply_symm_apply]
  refine ⟨a, GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, ha1, mul_zero]) (ι.injective ?_), ha1,
    fun v => GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ (ι.injective ?_)⟩
  · rw [RingHom.map_mul, map_mul, ha3]
    exact GlobalTheory.PlaceIdem.adele_ext fun Q => hff Q
  · rw [← hp v, RingHom.map_mul, RingHom.map_mul, hinf, mul_zero, mul_zero]
  · rw [← hp v, RingHom.map_mul, RingHom.map_mul, map_mul, map_mul, ha3]
    refine GlobalTheory.PlaceIdem.adele_ext fun Q => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap, GlobalTheory.PlaceIdem.mul_ap]
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · subst hQ; rfl
    · rw [h0 v Q hQ, mul_zero, mul_zero]

theorem exists_select (D : D7) : ∃ a : Formalism.L2.Theta.AE D, a * a = a ∧ infPart D a = 0 ∧
    (∀ v ε, NonSplitAt D v ε → a * algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε = 0) ∧
    ∀ e, IsSplitIdem D e → a * (e + cA D e) = e ∨ a * (e + cA D e) = cA D e := by
  classical
  obtain ⟨a, h1, h2, h3⟩ := exists_glue D (fun v => if h : ∃ e, SplitAt D v e then h.choose else 0)
    (fun v => by
      split_ifs with h
      · exact h.choose_spec.1
      · exact mul_zero _)
    (fun v => by
      split_ifs with h
      · rw [mul_comm]; exact h.choose_spec.pl_mul
      · exact zero_mul _)
  refine ⟨a, h1, h2, fun v ε h => ?_, fun e he => ?_⟩
  · rw [eq_single h.1, h3, dif_neg]
    rintro ⟨e, he⟩
    exact h.2 ⟨e, (isSplitIdem_iff e).2 ⟨v, he⟩, by rw [eq_single h.1, he.2.2]⟩
  · obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 he
    have h : ∃ e, SplitAt D v e := ⟨e, he⟩
    rw [he.2.2, h3, dif_pos h]
    exact (h.choose_spec.unique he).imp Eq.symm Eq.symm

theorem char_norm {D : D7} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n)
    (x y : (Formalism.L2.Theta.AE D)ˣ) (hy : (y : Formalism.L2.Theta.AE D) = x * cA D x) : χ y = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have := D.host.isCMField_hostE
  have e : y = idF D (Units.map (Algebra.norm (AF D.host.F) : Formalism.L2.Theta.AE D →* AF D.host.F) x) :=
    Units.ext (hy.trans (GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F)
      (x : Formalism.L2.Theta.AE D)).symm)
  rw [e, h η hη, hη.2.2.1, one_pow]

set_option maxHeartbeats 800000 in

theorem exists_split_character : ∀ (D : D7) (V : HSp D) (χ : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ ν : Formalism.L2.Theta.GA D V →* Circle, Continuous ν ∧ (∀ g ∈ GinfC V, ν g = 1) ∧ (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ∀ x, IsDetAt e V g x → ν g = χ x := by
  intro D V χ n hχ hres
  obtain ⟨a, haa, hinf, hns, hsp⟩ := exists_select D
  haveI : IsTopologicalRing (Formalism.L2.Theta.AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  let d : Formalism.L2.Theta.GA D V →* (Formalism.L2.Theta.AE D)ˣ := Matrix.GeneralLinearGroup.det.comp (matHom V)
  have hd : ∀ g, (d g : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det := fun _ => rfl
  have hc : Continuous d := Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val
  have htriv : ∀ g, (∀ i j, a * (Formalism.L2.Theta.mt V g - 1) i j = 0) → χ (cut a haa (d g)) = 1 := fun g hg => by
    have : cut a haa (d g) = 1 := Units.ext (by
      rw [cut_val, hd, mul_det a _ hg, add_sub_cancel, Units.val_one])
    rw [this, map_one]
  refine ⟨χ.comp ((cut a haa).comp d), hχ.1.comp ((continuous_cut a haa).comp hc), fun g hg => htriv g fun i j => ?_,
    fun v ε h g hg => htriv g fun i j => ?_, fun e he g hg x hx => ?_⟩
  · refine GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
    have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
    rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]
  · rw [← hg i j, ← mul_assoc, hns v ε h, zero_mul]
  · show χ (cut a haa (d g)) = χ x
    have hout := mul_det (1 - (e + cA D e)) (Formalism.L2.Theta.mt V g) fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]
    have hx' : (x : Formalism.L2.Theta.AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
    rcases hsp e he with h | h
    · congr 1
      refine Units.ext ?_
      rw [cut_val, hd, hx']
      linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
    · have hy : (cut a haa (d g) : Formalism.L2.Theta.AE D) = cA D e * (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
        rw [cut_val, hd]
        linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
      have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he.1]
      have hu := det_conj_mul V g
      have h1 : (cut a haa (d g) : Formalism.L2.Theta.AE D) * cA D x = 1 := by
        rw [hy, hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
        generalize (Formalism.L2.Theta.mt V g).det = z at hu
        linear_combination (z * cA D z - z - cA D z + 1) * hcc + cA D e * hu
      have h2 := char_norm hres x (x * (cut a haa (d g))⁻¹) (by
        rw [Units.val_mul, Units.inv_eq_of_mul_eq_one_right h1])
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2.symm

end GlobalTheory.SplitDetChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareGroupSchemePullback
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqPull

theorem tensor_isPullback {S : Scheme.{0}} (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback _ _

theorem sq_of_grpPullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  intro S S₀ f B _ B₀ _ i h
  obtain ⟨hP, hM⟩ := h
  let T : Over S₀ := B₀ ⊗ B₀
  have hw : ∀ x : T ⟶ B₀, (x.left ≫ i) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
    intro x
    rw [Category.assoc, hP.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((fst B₀ B₀).left ≫ i) (hw _)
  let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((snd B₀ B₀).left ≫ i) (hw _)
  have h1 : (lift x₀ y₀).left ≫ (fst B B).left = (fst B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift x₀ y₀).left ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨(lift x₀ y₀).left, ?_, ?_, h1, h2⟩
  · have outer : IsPullback ((snd B₀ B₀).left ≫ i) (fst B₀ B₀).left B.hom (B₀.hom ≫ f) :=
      IsPullback.paste_horiz (tensor_isPullback B₀ B₀).flip hP
    have sq : IsPullback (lift x₀ y₀).left (fst B₀ B₀).left (fst B B).left i := by
      refine IsPullback.of_right (h₁₂ := (snd B B).left) (v₁₃ := B.hom) (h₂₂ := B.hom) ?_ h1
        (tensor_isPullback B B).flip
      rw [h2, hP.w]
      exact outer
    exact IsPullback.paste_vert sq hP
  · have := hM T (fst B₀ B₀) (snd B₀ B₀) x₀ y₀ rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at this
    exact this

end GlobalTheory.SqPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTqLevelZeroOfTorusExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Raynaud

theorem exists_tq_level_zero_of_torusExtension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G], Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) →
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
      Nonempty (TQ (thickObj R (maximalIdeal R) 0 G) X) := by
  intro R _ _ G _ _ hT
  obtain ⟨E, ⟨d⟩⟩ := exists_splitExt_isGt_of_torusExtension (ResidueField R) _ hT
  have := E.free
  have := E.finite
  refine ⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨Q₁, -⟩ := exists_tq_of_gtDatum _ E _ d
  let r : Sp (R ⧸ maximalIdeal R ^ (0 + 1)) ⟶ Sp (ResidueField R) :=
    spMap (Ideal.Quotient.factor (show maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) by simp))
  have hr : r ≫ spMap (residue R) = thick R (maximalIdeal R) 0 := by
    rw [← Spec.map_comp]
    rfl
  let F : (thickObj R (maximalIdeal R) 0 G).left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)
  obtain ⟨Q₀, -⟩ := exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).congr hr.symm (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) Q₁
  exact ⟨Q₀⟩

example : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TQ (thickObj R (maximalIdeal R) 0 G) X) :=
  exists_tq_level_zero_of_torusExtension

end GlobalTheory.Raynaud

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTorsionLiftOfHenselian
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_torsion_lift_of_henselian : ∀ (W : Type) [CommRing W] [HenselianLocalRing W] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (p : Sp W ⟶ S) (N : ℕ), IsUnit (N : W) → ∀ x₀ : Over.mk (spMap (residue W) ≫ p) ⟶ G, x₀ ^ N = 1 → ∃! x : Over.mk p ⟶ G, x ^ N = 1 ∧ spMap (residue W) ≫ x.left = x₀.left := by
  intro W _ _ S G _ _ hG p N hN x₀ hx₀
  have := hG.smooth
  let G' := (Over.pullback p).obj G
  have : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom p))
  have hN' : IsUnit (N : Γ(Sp W, ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom
  have : Etale (mulN G' N).left := GrpTangent.etale_mulN G' hN'
  let T : Over (Sp W) := Over.mk (𝟙 (Sp W))
  let T₀ : Over (Sp W) := Over.mk (spMap (residue W))
  let r : T₀ ⟶ T := Over.homMk (spMap (residue W)) (by simp [T, T₀])
  let e := TorsionLift.ptsEquiv p G T p (Category.id_comp p)
  let e₀ := TorsionLift.ptsEquiv p G T₀ (spMap (residue W) ≫ p) rfl
  have hpow : ∀ {Z : Over (Sp W)} (y : Z ⟶ G'),
      y ^ N = 1 ↔ y.left ≫ (mulN G' N).left = (1 : Z ⟶ G').left := by
    intro Z y
    rw [← GrpTangent.comp_mulN]
    exact ⟨fun h => by rw [← Over.comp_left, h],
      fun h => Over.OverMorphism.ext (by rw [Over.comp_left, h])⟩
  have key : ∀ y₀ : T₀ ⟶ G', y₀ ^ N = 1 → ∃! y : T ⟶ G', y ^ N = 1 ∧ r ≫ y = y₀ := by
    intro y₀ hy₀
    have hone : (1 : T₀ ⟶ G').left = spMap (residue W) ≫ (1 : T ⟶ G').left := by
      rw [← comp_one r, Over.comp_left]
      rfl
    obtain ⟨l, ⟨hl₁, hl₂⟩, hl₃⟩ := existsUnique_lift_of_etale_of_henselian (mulN G' N).left
      (residue W) residue_surjective y₀.left (1 : T ⟶ G').left
      (by rw [(hpow y₀).1 hy₀, hone])
    have hlw : l ≫ G'.hom = T.hom := by
      rw [← Over.w (mulN G' N), ← Category.assoc, hl₂]
      exact Over.w _
    refine ⟨Over.homMk l hlw, ⟨(hpow _).2 hl₂, Over.OverMorphism.ext hl₁⟩, ?_⟩
    rintro y ⟨hy₁, hy₂⟩
    exact Over.OverMorphism.ext (hl₃ y.left ⟨congrArg Over.Hom.left hy₂, (hpow y).1 hy₁⟩)
  have h := key (e₀.symm x₀) (by rw [← map_pow, hx₀, map_one])
  refine (e.toEquiv.existsUnique_congr fun y => ?_).1 h
  change _ ↔ e y ^ N = 1 ∧ _ ≫ (e y).left = _
  rw [← map_pow, map_eq_one_iff e e.injective, MulEquiv.eq_symm_apply]
  refine and_congr_right fun _ => ?_
  have : (e₀ (r ≫ y)).left = spMap (residue W) ≫ (e y).left := by
    rw [TorsionLift.ptsEquiv_left, TorsionLift.ptsEquiv_left, Over.comp_left, Category.assoc]
    rfl
  rw [← this]
  exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_ringClassGroup_of_conductor_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  first | exact @GlobalTheory.CMVal.PicFin.finite_picO | exact GlobalTheory.CMVal.PicFin.finite_picO | (intros; apply GlobalTheory.CMVal.PicFin.finite_picO <;> assumption)
end

