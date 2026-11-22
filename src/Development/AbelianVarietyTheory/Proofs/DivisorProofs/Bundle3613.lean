import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3607
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3514
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3609
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyTrivialOfQuotientPullbackTrivialStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFamily_trivial_of_quotient_pullback_trivial : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  first | exact @GlobalTheory.DualInjPull.triv_of_triv_pull | exact GlobalTheory.DualInjPull.triv_of_triv_pull | (intros; apply GlobalTheory.DualInjPull.triv_of_triv_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelSmallSectionsChangeOfMetricStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → GoodFam P D (gdeg P.L D / D.factorial) (fun m => P.H m 1) → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation | exact GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation | (intros; apply GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitsFourierTermsAllLevelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classical_traits_fourier_terms_all_levels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), PosW W → (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → Φ.Four W (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.Poinc.four_of_classical | exact GlobalTheory.Poinc.four_of_classical | (intros; apply GlobalTheory.Poinc.four_of_classical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClsOpen

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ClsOpen

open GlobalTheory.ClsOpen in

theorem GlobalTheory.clsOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  intro E _ _ _ H Dw l Xo c φ D' L R V _ _ _ _ _ _ hR hV C t₁ P₁ iw θ hθ hb m N s ε e₁ e hε hs hu hD₁ hD
  set f : R := ∏ i, s (.inl i) with hf_def
  have hθf : θ f ≠ 0 := by rw [hf_def, map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hs i
  have hf0 : f ≠ 0 := fun h => hθf (by rw [h, map_zero])
  have hsk : ∀ k, s k ≠ 0 := by
    rintro (i | j)
    · exact fun h => hs i (by rw [h, map_zero])
    · exact (hu j).ne_zero
  have hθk : ∀ k, θ (s k) ≠ 0 := by
    rintro (i | j)
    · exact hs i
    · exact ((hu j).map θ).ne_zero
  let A := Localization.Away f
  have hpow : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain A := IsLocalization.isDomain_localization hpow
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers f) A hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A (Submonoid.powers f) hpow
  have hψ := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ hD₁ f (by
    rintro (i | j)
    · exact ⟨1, by rw [pow_one, hf_def]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)⟩
    · exact ⟨0, (hu j).dvd⟩)
  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap (algebraMap R A)) t₁
  obtain ⟨hpr, ham, hkt⟩ := GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate R hR t₁ P₁ f hψ tO mO
  have htors : GlobalTheory.TChart.TorsRat tO.G l.M' :=
    (GlobalTheory.TorsAway.torsRat_away_iff R f t₁.G tO.G mO.φ mO.cart l.M').1 (GlobalTheory.T.genericFibre_torsion_rational_of_base L R hR t₁ P₁ iw s ε e₁ hε hsk hD₁)
  let K := FractionRing V
  have hunitK : IsUnit (((algebraMap V K).comp θ) f) := by
    rw [RingHom.comp_apply]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hθf)
  let g : A →+* K := IsLocalization.Away.lift f hunitK
  have hg : g.comp (algebraMap R A) = (algebraMap V K).comp θ := IsLocalization.lift_comp _
  let bA : c.F →+* A := (algebraMap R A).comp (iw.comp L.b)
  let incl := (IntermediateField.inclusion c.le).toRingHom
  have hgb : g.comp bA = (algebraMap V K).comp C.b := by
    show g.comp ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [← RingHom.comp_assoc, hg, RingHom.comp_assoc, hb]
  have E1 : spMap g ≫ spMap (algebraMap R A) = jK V ≫ spMap θ :=
    (spMap_comp' _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp' _ _))
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ (C.y ≫ pullback.fst _ _)
  have hsK : (C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap g ≫ spMap (bA.comp incl) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, spMap_comp' incl bA, ← Category.assoc,
      ← spMap_comp' bA g, hgb, spMap_comp']
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := (genOf_iff Xo c C.y C.t).1 C.gen
  obtain ⟨bc⟩ := GlobalTheory.T.exists_tripleMap_of_same_uniformised_coords L R V hR hV t₁ P₁ C.t C.P iw θ hθ s ε e₁ e hθk hD₁ hD
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl bc m₁
  obtain ⟨n₃⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) n₂ n₁
  obtain ⟨n₄⟩ := GlobalTheory.TraitOrder.cancel E1 mO n₃
  obtain ⟨o, ho, ⟨mo⟩⟩ := GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain Dw l c A bA tO hpr ham hkt htors K g _ oK hsK n₄
  obtain ⟨f₀, ⟨hf₀s, ⟨mf₀⟩⟩, -⟩ := Xo.rep (Sp A) (spMap (bA.comp incl)) inferInstance o
  have hf₀ : f₀ ≫ Xo.s = spMap bA ≫ spMap incl := by rw [hf₀s, spMap_comp']
  let yo : Sp A ⟶ Xo.XF c := pullback.lift f₀ (spMap bA) hf₀
  have hκ : spMap g ≫ yo = C.y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      obtain ⟨mk'⟩ := GlobalTheory.LevelQuotRep.obj_comp mo mf₀
      exact (Xo.rep (Sp K) _ inferInstance oK).unique ⟨by rw [Category.assoc, hf₀s, hsK], ⟨mk'⟩⟩ ⟨rfl, ⟨mK⟩⟩
    · rw [Category.assoc, pullback.lift_snd, C.y_over, ← spMap_comp', hgb, spMap_comp']
  have hunitR : IsUnit ((algebraMap R (FractionRing R)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf0)
  let jA : A →+* FractionRing R := IsLocalization.Away.lift f hunitR
  have hjA : jA.comp (algebraMap R A) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hg₀ : spMap jA ≫ spMap (algebraMap R A) = jK R := by rw [← spMap_comp', hjA]
  have mo' : SABMap tO Xo.univ.t f₀ := ho ▸ mf₀.toSABMap
  refine ⟨spMap jA ≫ yo, yo, spMap g, ?_, ?_, ?_, E1, hκ⟩
  · rw [Category.assoc, pullback.lift_snd, ← hg₀, Category.assoc]
    show spMap jA ≫ spMap ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [spMap_comp']
  · refine (genOf_iff Xo c _ t₁).2 ?_
    obtain ⟨t', ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap jA) tO
    exact ⟨t', GlobalTheory.TraitOrder.comp hg₀ mO n,
      GlobalTheory.TraitOrder.comp (by rw [Category.assoc, pullback.lift_fst]) mo' n⟩
  · intro g' hg'
    obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
    have h2 : CommRingCat.ofHom (algebraMap R A) ≫ φ' = CommRingCat.ofHom (algebraMap R (FractionRing R)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact hg')
    have h3 : φ'.hom = jA := IsLocalization.ringHom_ext (Submonoid.powers f)
      ((congrArg CommRingCat.Hom.hom h2).trans hjA.symm)
    have h4 : φ' = CommRingCat.ofHom jA := by ext1; exact h3
    rw [h4]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPerfectOrthogonalOfKernelsZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.perfect_and_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro hHdR R _ A B _ _ g hA hB hgA hgB P hP φ hφ
  exact ⟨GlobalTheory.T.pairing_isPerfect_abelianSchemes_both_kernels_zero hHdR R A B g hA hB hgA hgB P hP φ hφ,
    GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hHdR R A B g hA hB hgA hgB P hP.isLB φ hφ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension
section
namespace GlobalTheory

theorem deRhamVectorExtension : GlobalTheory.Published.DeRhamVectorExtension :=
  GlobalTheory.T.deRhamVectorExtensionIso_of_hodgeDeRham GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperUnitaryLevelGaloisActsOnLabelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deeperUnitaryLevel_galois_acts_on_labels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → UIsLab D.X (D.lift ct (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (a x) := by
  first | exact @GlobalTheory.UPoinc.UGalLab.main | exact GlobalTheory.UPoinc.UGalLab.main | (intros; apply GlobalTheory.UPoinc.UGalLab.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneratingFamily_data_from_base_algClosed_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (s : Fin C.m ⊕ Fin N → V), D'.p + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.p ∧ D'.q + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.q ∧ IsLocalHom θ₀ ∧ θ₀.comp L.b = C.b ∧ (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) ∧ (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  first | exact @GlobalTheory.VData.exists_divFrom | exact GlobalTheory.VData.exists_divFrom | (intros; apply GlobalTheory.VData.exists_divFrom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerFibreConjugateEvaluationIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8Power_fibre_conjugate_evaluation_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) ∧ (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  first
  | exact @GlobalTheory.Poinc.Sep.sharp_fibre_conj_iso
  | intro g l hl hlo W hW
    obtain ⟨jB, hB⟩ := GlobalTheory.T.theta_series_sharp_reference_sixteen_terms g l hl hlo W hW
    obtain ⟨jD, hD⟩ := GlobalTheory.T.fibre_iso_carries_sharp_points_to_conjugates g l hl hlo W hW
    refine ⟨max jB jD, fun j hj V V₁ _ _ _ _ _ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr σ hσ => ?_⟩
    obtain ⟨f, h0, h1, h2⟩ :=
      hB j (le_of_max_le_left hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ
    exact ⟨f, h0, h1, h2,
      hD j (le_of_max_le_right hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ f h0 h1
        (fun y hy => h2 y ⟨j * 2, by rw [pow_mul]; exact hy⟩)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechKodairaSpencerClassAbelianTriple
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSExists

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} (h : W₁ ≤ W₀) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h), fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

theorem isField_sub {Z : Scheme.{0}} {W₀ : Z.Opens} {d d' : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) (hd' : IsField W₀ d') : IsField W₀ (fun W f => d W f - d' W f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · simp only [hd.1 W hW, hd'.1 W hW]; ring
  · simp only [hd.2.1 W hW, hd'.2.1 W hW]; ring
  · simp only [map_sub, hd.2.2 W W' h hW, hd'.2.2 W W' h hW]

theorem lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := GlobalTheory.T.exists_vectorField_lifts_affine_cover_smooth_group

theorem cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := GlobalTheory.T.cechCocycle_verticalFields_eq_coboundary_add_logDerivatives

theorem exists_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t ⊤ U v D Θ := by
  intro E _ _ _ H X t hP hA hK U n v hv hb D
  obtain ⟨J, W, j, d, hWa, hcov, hWj, hd, hlift⟩ := lifts E H X t U D
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i => hcov ▸ le_iSup W i
  have hres : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i)
      ((t.G.hom.appLE U.1 (W i) (hWU i)).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i) (homOfLE (inf_le_left : W i ⊓ W i' ≤ W i)).op)
  have hres' : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i')
      ((t.G.hom.appLE U.1 (W i') (hWU i')).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i') (homOfLE (inf_le_right : W i ⊓ W i' ≤ W i')).op)
  have a1 : ∀ i i' (r : Γ(X, U.1)), d i (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres i i' r, (hd i).2.2 _ _ inf_le_left le_rfl, hlift i (hWU i), hres]
  have a2 : ∀ i i' (r : Γ(X, U.1)), d i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres' i i' r, (hd i').2.2 _ _ inf_le_right le_rfl, hlift i' (hWU i'), hres']
  obtain ⟨Θ, h, hh, hhv, hks⟩ := cocycle E H X t hP hA hK U n v hv hb J W j hWa hcov hWj
    (fun i i' O f => d i O f - d i' O f)
    (fun i i' => isField_sub (isField_mono inf_le_left (hd i)) (isField_mono inf_le_right (hd i')))
    (fun i i' hW r => by
      show d i _ _ - d i' _ _ = 0
      rw [a1, a2, sub_self])
    (fun i i' i'' O _ f => sub_add_sub_cancel _ _ _)
  refine ⟨Θ, J, W, j, fun i O f => d i O f - h i O f, by rw [inf_top_eq]; exact hcov, hWj,
    fun i => isField_sub (hd i) (hh i), fun i hW r => ?_, fun i i' O hO f S _ φ g₀ w hg hO' hw => ?_⟩
  · show d i _ _ - h i _ _ = _
    rw [hlift i hW r, hhv i hW r, sub_zero]
  · have e := hks i i' O hO f S φ g₀ w hg hO' hw
    have hv' : ∀ a b : Γ(t.G.left, O), valR g₀ O (a - b) = valR g₀ O a - valR g₀ O b := fun a b => by
      simp only [valR, dif_pos hO', map_sub]
    show valR g₀ O ((d i O f - h i O f) - (d i' O f - h i' O f)) = _
    rw [show (d i O f - h i O f) - (d i' O f - h i' O f) = (d i O f - d i' O f) - (h i O f - h i' O f) by ring,
      hv', e]
    ring

end GlobalTheory.KSExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeEquivTwoMembersSamePointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_equiv_two_members_same_point : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (m₀ : ℕ) (t₀ : Fin m₀ → V₀) (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ K : (Fin 8 → X₀) ≃+ (Fin 8 → X), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) ∧ ∀ a mu, 𝔪₀.YY a mu → 𝔪.YY a (K mu) := by
  first | exact @GlobalTheory.Poinc.Sep.Cmp.exists_latEquiv_of_members | exact GlobalTheory.Poinc.Sep.Cmp.exists_latEquiv_of_members | (intros; apply GlobalTheory.Poinc.Sep.Cmp.exists_latEquiv_of_members <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialDefectHeatOperatorMonomialStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_defect_heatOperator_monomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  first | exact @GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial | exact GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial | (intros; apply GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial <;> assumption)
end

