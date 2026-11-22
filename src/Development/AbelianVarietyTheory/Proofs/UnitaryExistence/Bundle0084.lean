import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ContinuousIffCrdA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OnlySecondOfFormLaws
section
noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def DatumSign {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) {r : ℕ} (V' : ConjugateFieldNorm.HSpace D.host.E r)
    (ε : ℤˣ) : Prop :=
  ∃ φ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), Function.Injective φ ∧
    LinearMap.range φ = ConjugateFieldNorm.latAt D.host.F D.host.AA V' 1 ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (-D.host.xi0 * herm V'.Gm (φ x) (φ y))

theorem invProb_iff (V : HSp D) (hP : VolPairEx V) (hV : FinVol V) (ν : Measure (AutQ V)) :
    IsProbabilityMeasure ν ∧ RightInv V ν ↔ ν = muQ1 V := by
  have hp := volPair_isVolPair V hP
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.lcsc_adelic_unitary_group _ _ D.sp.cm.sig _ V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : (volPair V).1.IsHaarMeasure := hp.1.1
  have hV' := hV
  rw [FinVol, muQ_univ] at hV'
  have hq : muQ1 V = ((volPair V).1 (volPair V).2)⁻¹ • ((volPair V).1.restrict (volPair V).2).map (autMk V) := by
    rw [muQ1, if_pos (show _ ∧ _ from hV), muQ_univ]; rfl
  constructor
  · rintro ⟨h1, h2⟩
    rw [hq]
    exact GlobalTheory.T.invariant_probability_lattice_quotient_unique _ (GQ V) _ _ hp.2 hV'.2 ν h2
  · rintro rfl
    refine ⟨inferInstance, fun h ρ hρ s hs => ?_⟩
    have hm := autMk_measurable V
    have e : autMk V ⁻¹' (ρ ⁻¹' s) = (· * h) ⁻¹' (autMk V ⁻¹' s) := by
      ext g; exact iff_of_eq (congrArg (· ∈ s) (hρ g))
    have hs' : MeasurableSet (ρ ⁻¹' s) := by
      change MeasurableSet (autMk V ⁻¹' (ρ ⁻¹' s))
      rw [e]; exact measurable_mul_const h (hm hs)
    have hri := GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) _ hp.2 hV'.1 hV'.2
    have : (volPair V).1.IsMulRightInvariant := ⟨hri⟩
    have hF : IsFundamentalDomain (GQ V) ((Equiv.mulRight h⁻¹) ⁻¹' (volPair V).2) (volPair V).1 :=
      hp.2.preimage_of_equiv (measurePreserving_mul_right _ h⁻¹).quasiMeasurePreserving (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) (volPair V).1
    rw [hq, Measure.smul_apply, Measure.smul_apply]
    congr 1
    rw [show ((volPair V).1.restrict (volPair V).2).map (autMk V) s = _ from
      congrArg (fun m : Measure (AutQ V) => m s) (GlobalTheory.AutQuotCheck.map_restrict_eq (GQ V) _ hp.2 hF),
      Measure.map_apply hm hs', Measure.map_apply hm hs, Measure.restrict_apply (hm hs'),
      Measure.restrict_apply (hm hs), e, ← measure_preimage_mul_right (volPair V).1 h (_ ∩ _ ⁻¹' _)]
    congr 1
    ext g
    simp

def numsOf (D : D7) : ConjugateFieldNorm.Nums D.host.E where
  k := D.R.k
  m := D.R.m
  g := D.host.g
  g_prime := D.host.g_prime
  g_ne := D.host.g_ne
  Nc := Ideal.absNorm D.host.ccK
  Nc_pos := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 D.host.ccK_ne_bot)
  AA := D.host.AA
  Os := D.what₂.phiO.range

def SpaceW (T : Core D) : Prop := ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j

def spW (D : D7) (j : (numsOf D).J) : ConjugateFieldNorm.HSpace D.host.E D.R.r := spOf (D.sp.W j) (D.sp.W_rank j j.2.1 j.2.2)

variable {T : Core D} (hW : SpaceW T)

def psi (j : (numsOf D).J) {σ} (hσ : GoodEmb T.Q.c σ) : ConjugateFieldNorm.GA D.host.F (spW D j) ≃* GA D (T.V j σ) :=
  (exists_isCoord (T.V j σ) (hW j j.2 σ hσ) (D.sp.W_rank j j.2.1 j.2.2)).choose

def parOf (π : Fin 2 → 𝓞 D.host.E) : ConjugateFieldNorm.CorePar D.host.F (numsOf D) where
  H := T.Q.H
  l := T.Q.l
  c := T.Q.c
  Dw j := T.Q.Dw j
  Xo j := T.Q.Xo j
  U j σ := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)
  V j := spW D j
  dict j σ hσ g := T.dict j σ (psi hW j hσ g)
  mu j σ hσ g := T.mu j σ (psi hW j hσ g)
  Kf j := (T.Kf j T.σ₀).comap (psi hW j T.good_σ₀).toMonoidHom
  pi := π

def GenBy (T : Core D) (π : Fin 2 → 𝓞 D.host.E) : Prop :=
  ∀ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = Ideal.span {T.Q.H.bar (π k)}

def RecTies : Prop :=
  T.Q.H.d = D.host.d ∧ (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ T.Q.PinField ∧
    ∀ (j : (numsOf D).J) σ (hσ : GoodEmb T.Q.c σ),
      (T.Kf j σ).comap (psi hW j hσ).toMonoidHom = (T.Kf j T.σ₀).comap (psi hW j T.good_σ₀).toMonoidHom

def ArchEquiv (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Prop :=
  ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    ∃ x0 : ∀ c, Frame ((T.U j σ).X c).Ψ D.R.r, (∀ c, x0 c ∈ ((T.U j σ).X c).dom ∧ ∃ g, T.dict j σ g = ⟨c, x0 c⟩) ∧
      ∀ g, ∀ h ∈ GinfC (T.V j σ), ∃ γ' ∈ ((T.U j σ).X (T.dict j σ g).1).Γ,
        T.dict j σ (g * h) = ⟨(T.dict j σ g).1,
          lact γ' (rmul (T.dict j σ g).2 (archMat (T.V j σ) th hr x0 h (T.dict j σ g).1))⟩

def OnlyFirst (T : Core D) : Prop :=
  ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → Continuous (T.mu j σ) ∧ ArchEquiv T j σ

def OnlySecond (π : Fin 2 → 𝓞 D.host.E) : Prop :=
  (∀ i, π i ∈ Algebra.adjoin ℤ {T.Q.H.w0} ∧ π i * T.Q.H.bar (π i) = (D.host.g i : 𝓞 D.host.E)) ∧
  ∀ j : (numsOf D).J, ((∃ ε, DatumSign (T.Q.Dw j) (spW D j) ε) → DatumSign (T.Q.Dw j) (spW D j) 1) ∧
    (∀ σ (hσ : GoodEmb T.Q.c σ), (IsUnf (T.U j σ) → (parOf hW π).PinDict j σ hσ) ∧
      ∀ g : ConjugateFieldNorm.GA D.host.F (spW D j), g.1.1.val.det = 1 → g.2.1.val.det = 1 → (parOf hW π).mu j σ hσ g = 1) ∧
    AutomorphismGroupTopologies.WeightField (parOf hW π) j ∧ AutomorphismGroupTopologies.FrameExt (parOf hW π) j ∧ AutomorphismGroupTopologies.PtOnComp (parOf hW π) j

variable (π : Fin 2 → 𝓞 D.host.E)

end GlobalTheory.CoreLawsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.CubeGlue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem triv_of_triv_pull_id {P : Scheme.{0}} {M : LB P} (h : Triv (M.pull (𝟙 P))) : Triv M := by
  obtain ⟨u, hu⟩ := h
  have le : ∀ i, M.U i ≤ (M.pull (𝟙 P)).U (fun _ => i) := fun i y hy => mem_pull.2 hy
  refine ⟨⟨fun i => res (le i) (u.s fun _ => i)⟩, fun i j => unit_ext fun y hy => ?_⟩
  have c := gen_trans hu (𝟙 P) y (le i hy.1) (le j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (c.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))

theorem exists_section {P Z : Scheme.{0}} (p : P ⟶ Z) (e : Z ⟶ P) (he : e ≫ p = 𝟙 Z) (V : Z.Opens) :
    ∃ s : V.toScheme ⟶ (p ⁻¹ᵁ V).toScheme, s ≫ (p ⁻¹ᵁ V).ι = V.ι ≫ e ∧ s ≫ (p ∣_ V) = 𝟙 _ := by
  obtain ⟨s, hs⟩ : ∃ s : V.toScheme ⟶ (p ⁻¹ᵁ V).toScheme, s ≫ (p ⁻¹ᵁ V).ι = V.ι ≫ e :=
    ⟨IsOpenImmersion.lift _ (V.ι ≫ e) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (· ∈ V) (congrArg (fun m => m q.1) he)).mpr q.2), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨s, hs, ?_⟩
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs, Category.assoc, he,
    Category.id_comp, Category.comp_id]

theorem exists_normalised {P Z : Scheme.{0}} {M : LB P} (hM : M.IsLB) (p : P ⟶ Z) (e : Z ⟶ P) (he : e ≫ p = 𝟙 Z)
    (g : LB.Gen (M.pull e)) (hg : g.IsGen) (V : Z.Opens) (h : Triv (M.pull (p ⁻¹ᵁ V).ι)) :
    ∃ t : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => (p ⁻¹ᵁ V).ι ≫ 𝟙 P) (fun _ => 1)), t.IsGen ∧
      ∀ (T : Scheme.{0}) (r : T ⟶ (p ⁻¹ᵁ V).toScheme) (b : T ⟶ Z) (z : T) (J), Good M z J →
        r ≫ (p ⁻¹ᵁ V).ι = b ≫ e → val t r z J = val g b z J := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs, -⟩ := exists_section p e he V
  have n₁ : ((p ∣_ V) ≫ s) ≫ (p ⁻¹ᵁ V).ι = ((p ⁻¹ᵁ V).ι ≫ p) ≫ e := by
    rw [Category.assoc, hs, ← Category.assoc, morphismRestrict_ι]
  obtain ⟨t', ht', hv⟩ := exists_gen hM (K' := PUnit) (φ' := fun _ => (p ⁻¹ᵁ V).ι ≫ 𝟙 P) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁, Category.comp_id]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ t (LB.invGen M _ _ (LB.pullGen M _ _ t ((p ∣_ V) ≫ s))))
      (LB.pullGen M _ _ g ((p ⁻¹ᵁ V).ι ≫ p)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hg _))
  refine ⟨t', ht', fun T r b z J hJ hr => ?_⟩
  have hb : r ≫ (p ⁻¹ᵁ V).ι ≫ p = b := by
    rw [← Category.assoc, hr, Category.assoc, he, Category.comp_id]
  have : r ≫ (p ∣_ V) ≫ s = r := by
    rw [← cancel_mono (p ⁻¹ᵁ V).ι, Category.assoc, n₁, ← Category.assoc, hb, hr]
  rw [hv T r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, this, mul_inv_cancel, hb,
    _root_.one_mul]

theorem triv_of_locally_triv {P Z : Scheme.{0}} {M : LB P} (hM : M.IsLB) (p : P ⟶ Z) (e : Z ⟶ P)
    (he : e ≫ p = 𝟙 Z) (hp : ∀ V : Z.Opens, Function.Surjective (p ∣_ V).appTop.hom) (h₀ : Triv (M.pull e))
    (loc : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧ Triv (M.pull (p ⁻¹ᵁ V).ι)) : Triv M := by
  obtain ⟨g, hg⟩ := h₀
  choose U hU hT using loc
  choose t ht hn using fun z => exists_normalised hM p e he g hg (U z) (hT z)
  obtain ⟨u, hu, -⟩ := glue_gen hM (K := PUnit) (fun _ => 𝟙 P) (fun _ => 1) (fun s => p ⁻¹ᵁ U s)
    (fun y => ⟨p y, hU _⟩) t ht (by
      intro s s' T r r' z J hJ hr
      obtain ⟨σ, hσ, hσ'⟩ := exists_section p e he (U s ⊓ U s')
      let m := P.homOfLE (show p ⁻¹ᵁ (U s ⊓ U s') ≤ p ⁻¹ᵁ U s from fun _ hy => hy.1)
      let m' := P.homOfLE (show p ⁻¹ᵁ (U s ⊓ U s') ≤ p ⁻¹ᵁ U s' from fun _ hy => hy.2)
      have hm : m ≫ (p ⁻¹ᵁ U s).ι = (p ⁻¹ᵁ (U s ⊓ U s')).ι := P.homOfLE_ι _
      have hm' : m' ≫ (p ⁻¹ᵁ U s').ι = (p ⁻¹ᵁ (U s ⊓ U s')).ι := P.homOfLE_ι _
      obtain ⟨ρ, hρ⟩ : ∃ ρ : T ⟶ (p ⁻¹ᵁ (U s ⊓ U s')).toScheme, ρ ≫ (p ⁻¹ᵁ (U s ⊓ U s')).ι = r ≫ (p ⁻¹ᵁ U s).ι :=
        ⟨IsOpenImmersion.lift _ (r ≫ (p ⁻¹ᵁ U s).ι) (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
      have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
      have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
      have key := gen_unique' hM (K := PUnit) (K' := PUnit) (φ := fun _ => m ≫ (p ⁻¹ᵁ U s).ι ≫ 𝟙 P) (ε := fun _ => 1)
        (φ' := fun _ => m' ≫ (p ⁻¹ᵁ U s').ι ≫ 𝟙 P) (ε' := fun _ => 1)
        (fun W _ k => Finset.prod_congr rfl fun i _ => by
          show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
          rw [← Category.assoc, ← Category.assoc m, hm, hm'])
        (p ∣_ (U s ⊓ U s')) σ hσ' (hp _) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
        (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
          rw [val_pull hI, val_pull hI, hn s _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm, hσ]),
            hn s' _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm', hσ])]) T ρ z J hJ
      rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key)
  exact triv_of_triv_pull_id ⟨u, hu⟩

theorem surjective_restrict {P Z : Scheme.{0}} (p : P ⟶ Z) (h : ∀ V : Z.Opens, IsIso (p.app V)) (V : Z.Opens) :
    Function.Surjective (p ∣_ V).appTop.hom := by
  have : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    have := h (V.ι ''ᵁ ⊤)
    refine IsIso.comp_isIso' this ?_
    rw [eqToHom_op]; exact Functor.map_isIso _ _
  exact (ConcreteCategory.bijective_of_isIso (p ∣_ V).appTop).2

theorem triv_of_triv_faces : ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → Triv M := by
  intro k _ X Y Z x₀ y₀ z₀ sX sY pX pY jX jY gX gY cZ M hM h₁ h₂ h₃
  have loc := GlobalTheory.T.theorem_of_cube_locally_two_projective_factors k X Y Z x₀ y₀ z₀ sX sY pX pY jX jY gX gY cZ M hM h₁ h₂ h₃
  have iX : ∀ V, IsIso ((snd X (Y ⊗ Z)).left.app V) := fun V =>
    GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field (IsPullback.of_hasPullback X.hom (Y ⊗ Z).hom) V
  have iY : ∀ V, IsIso ((snd Y Z).left.app V) := fun V =>
    GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field (IsPullback.of_hasPullback Y.hom Z.hom) V
  let σ : Z ⟶ Y ⊗ Z := lift (toUnit Z ≫ y₀) (𝟙 Z)
  obtain ⟨g, hg⟩ := h₁
  refine triv_of_locally_triv hM (snd X (Y ⊗ Z) ≫ snd Y Z).left
    (σ.left ≫ (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) ?_ (surjective_restrict _ fun V => ?_)
    ⟨_, DVR.pullGen_isGen _ _ _ _ hg σ.left⟩ loc
  · rw [← Over.comp_left, ← Over.comp_left]
    exact congrArg (fun q => q.left)
      (show (σ ≫ lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))) ≫ snd X (Y ⊗ Z) ≫ snd Y Z = 𝟙 Z by simp [σ])
  · rw [Over.comp_left, Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' (iY V) (iX _)

end GlobalTheory.CubeGlue
end

