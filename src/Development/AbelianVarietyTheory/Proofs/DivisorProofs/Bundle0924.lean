import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isOpenEmbedding_entriesGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_entriesGLInf.measurableEmbedding.measurable_comp_iff).1
    (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j)
  exact hF.measurable.comp h

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem IsRapidFInf.integrable {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin n) (Cinf E)} {η : X → Z →L[ℝ] ℝ} (h : IsRapidFInf ν k γ η)
    {W : GL (Fin n) (Cinf E) → ℂ} (hW : IsModGrowthInf W) (z : Z) (g : GL (Fin n) (Cinf E)) :
    Integrable (fun x => k x * (𝐞 (η x z) : ℂ) * W (g * γ x)) ν := by
  obtain ⟨hc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  refine ((h.2.2.2 N).const_mul (C * htInf g ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Measurable.aestronglyMeasurable ((h.1.mul ?_).mul ?_)
    · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp (h.2.2.1 z)
    · exact measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop) h.2.1
  · rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    have h1 : htInf (g * γ x) ≤ htInf g * (htInf (γ x) * (1 + ‖η x‖)) :=
      (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (htInf_pos' _).le (by linarith [norm_nonneg (η x)])) (htInf_pos' _).le)
    have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
    rw [mul_pow] at h2
    calc ‖k x‖ * ‖W (g * γ x)‖ ≤ ‖k x‖ * (C * (htInf g ^ N * (htInf (γ x) * (1 + ‖η x‖)) ^ N)) :=
          mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = _ := by ring

theorem isKerOpInf_zero_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    IsKerOpInf (E := E) (n := n)
      (fun (_ : GL (Fin n) (Cinf E) → ℂ) (_ : Z) (_ : GL (Fin n) (Cinf E)) => (0 : ℂ)) := by
  refine ⟨Unit, inferInstance, 0, inferInstance, fun _ => 0, fun _ => 1, fun _ => 0, ?_, ?_⟩
  · exact ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_zero_measure⟩
  · intro W _ z g
    simp

theorem isKerOpInf_add_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ} (hT : IsKerOpInf T) (hT' : IsKerOpInf T') :
    IsKerOpInf (fun W z g => T W z g + T' W z g) := by
  obtain ⟨X, mX, ν, hν, k, γ, η, hr, hT⟩ := hT
  obtain ⟨X', mX', ν', hν', k', γ', η', hr', hT'⟩ := hT'
  have e1 : MeasurableEmbedding (Sum.inl : X → X ⊕ X') :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => measurableSet_inl_image.2 hs⟩
  have e2 : MeasurableEmbedding (Sum.inr : X' → X ⊕ X') :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.2 hs⟩
  refine ⟨X ⊕ X', inferInstance, ν.map Sum.inl + ν'.map Sum.inr, inferInstance, Sum.elim k k', Sum.elim γ γ',
    Sum.elim η η', ?_, ?_⟩
  · refine ⟨hr.1.sumElim hr'.1, fun i j => ?_, fun z => ?_, fun N => ?_⟩
    · have : (fun x : X ⊕ X' => ((Sum.elim γ γ' x : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
          Sum.elim (fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j)
            (fun x => (γ' x : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.1 i j).sumElim (hr'.2.1 i j)
    · have : (fun x : X ⊕ X' => Sum.elim η η' x z) = Sum.elim (fun x => η x z) (fun x => η' x z) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.2.1 z).sumElim (hr'.2.2.1 z)
    · rw [integrable_add_measure, e1.integrable_map_iff, e2.integrable_map_iff]
      exact ⟨hr.2.2.2 N, hr'.2.2.2 N⟩
  · intro W hW z g
    have i1 := hr.integrable hW z g
    have i2 := hr'.integrable hW z g
    show T W z g + T' W z g = _
    rw [integral_add_measure, e1.integral_map, e2.integral_map, hT W hW z g, hT' W hW z g]
    · rfl
    · rw [e1.integrable_map_iff]; exact i1
    · rw [e2.integrable_map_iff]; exact i2

theorem isKerOpInf_fintype_sum (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι]
    (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) (hT : ∀ i, IsKerOpInf (T i)) :
    IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  classical
  suffices h : ∀ s : Finset ι, IsKerOpInf (fun W z g => ∑ i ∈ s, T i W z g) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isKerOpInf_zero_sum (E := E) (n := n) (Z := Z))
  | insert a s ha ih =>
    have : (fun W z g => ∑ i ∈ insert a s, T i W z g) = fun W z g => T a W z g + ∑ i ∈ s, T i W z g := by
      funext W z g; rw [Finset.sum_insert ha]
    rw [this]
    exact isKerOpInf_add_sum (hT a) ih

example : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι] (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ),
    (∀ i, IsKerOpInf (T i)) → IsKerOpInf (fun W z g => ∑ i, T i W z g) := isKerOpInf_fintype_sum

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem pullbackGerm_finset_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {K : Type} (s : Finset K)
    (a : K → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem isMat_germ : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB R _ t A' B' _ _ φA' φB' Φ' c h
  obtain ⟨ψA, ψB, α, h1, h2, -, -, hch⟩ := h
  refine ⟨ψA, ψB, h1, h2, ?_⟩
  intro Z e z pM q hM hA
  have hz : e z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q) := by
    refine ⟨?_, ?_⟩
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hM i
      simpa using this
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hA i
      simpa using this
  refine ⟨gm e z _ (α.s (pM, q)), fun j => ?_⟩
  have E := congrArg (gs e z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q))) (hch j (pM, q))
  erw [gs_mul _ _ _ hz] at E
  erw [gs_unit _ _ _ hz, pullbackGerm_finset_sum _ _ _ hz, gs_appLE _ _ _ _ _ _ hz] at E
  refine E.trans (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  erw [gs_mul _ _ _ hz, gs_appLE _ _ _ _ _ _ hz, gs_appLE _ _ _ _ _ _ hz]
  rfl

end GlobalTheory.HomFixMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermitiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSndStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  first | exact @GlobalTheory.PicGlue.fnBij_snd | exact GlobalTheory.PicGlue.fnBij_snd | (intros; apply GlobalTheory.PicGlue.fnBij_snd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.ValuativeFlat

theorem isProper_of_lift_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s → Flat s → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* V) (x : Sp K ⟶ X), x ≫ s = spMap ((algebraMap V K).comp β) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (_ : Field L) (_ : Algebra V W) (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsLocalHom (algebraMap V W) ∧ ∃ f : Sp W ⟶ X, spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f) → IsProper s := by
  intro R _ _ _ _ X s hq hflat h
  have hq' : IsQProjOver (s ≫ 𝟙 (Sp R)) := by rwa [Category.comp_id]
  have hP := GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R X (Sp R) s (𝟙 _) inferInstance hq' ?_
  · exact hP
  intro V K _ _ _ _ _ _ _ x y hx hxy
  let β : R →+* V := (Spec.preimage y).hom
  have hy : y = spMap β := by simp [β, spMap]
  have hxs : x ≫ s = spMap ((algebraMap V K).comp β) := by
    rw [hxy, hy, spMap, spMap, ← Spec.map_comp]; rfl
  have hinj : Function.Injective ((algebraMap V K).comp β) :=
    GlobalTheory.T.injective_of_flat_point_at_generic_points R K X s x _ hflat hx hxs
  have : CharZero K := charZero_of_injective_ringHom hinj
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hloc, f, hf⟩ := h V K β x hxs
  exact GlobalTheory.T.descend_point_valuationRing_of_dominating_local_domain V K W L hc hloc X x f hf

end GlobalTheory.ValuativeFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafOfOpenImmersionLocalGlueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSheaf_of_open_immersion_local_glue : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → Presieve.IsSheaf Scheme.zariskiTopology F := by
  first | exact @GlobalTheory.isSheaf_of_local_glue | exact GlobalTheory.isSheaf_of_local_glue | (intros; apply GlobalTheory.isSheaf_of_local_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

noncomputable section

theorem reads_of_perC {D : D7} {r g : ℕ} (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (X : Data D.host.E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x x' : Frame X.Ψ r)
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (h : ∀ u, (fun j => perC X x' u (idx j)) = M *ᵥ fun j => perC X x u (idx j))
    (f : WO V W → ℂ) (φ : TF V.rank g) (hf : Reads θ V W hr X bas idx f φ x) :
    Reads θ V W hr X bas idx f ((M.det ^ (V.rank / 2)) • φ) x' := by
  have hP : ∀ s, perMat X bas idx s x' = M * perMat X bas idx s x := by
    intro s
    ext i k
    have := congrFun (h fun τ => Data.emb τ.1 (bas (Pi.single (s k) 1))) i
    exact this
  have hH : hMat X bas idx x' = hMat X bas idx x * M⁻¹ := by
    rw [hMat, hP, Matrix.mul_inv_rev, hMat]
  have hT : tauMat X bas idx x' = tauMat X bas idx x := by
    rw [tauMat, hH, hP, Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹, nonsing_inv_mul _ hM, Matrix.one_mul, tauMat]
  have hI : imInv X bas idx x' = imInv X bas idx x := by rw [imInv, imInv, hT]
  obtain ⟨⟨R, hR, h1, h2⟩, h3⟩ := hf
  refine ⟨⟨R, hR, fun y hy => h1 y fun e => hy (by simp [e]), fun y z hz => by simp [h2 y z hz]⟩, fun w hw => ?_⟩
  have hz : ∀ b, hMat X bas idx x' *ᵥ zOf θ V W hr X idx x' w b = hMat X bas idx x *ᵥ zOf θ V W hr X idx x w b := by
    intro b
    have : zOf θ V W hr X idx x' w b = M *ᵥ zOf θ V W hr X idx x w b := h _
    rw [this, hH, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  have hS : ∀ (c : ℂ) t z, thS (c • φ) t z = c * thS φ t z := by
    intro c t z
    simp only [thS, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]
  rw [h3 w hw]
  simp only [hx, thA, hz, hT, hI, hS]
  have hd : (hMat X bas idx x).det = (hMat X bas idx x').det * M.det := by
    rw [hH, ← det_mul, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  rw [hd, mul_pow]
  ring

theorem det_tr_inv_block {r : ℕ} (P Q b : Matrix (Fin r) (Fin r) ℂ) (hb : IsUnit b.det) (hPQ : P + Q = 1)
    (hPP : P * P = P) (hc : b * P = P * b) (hs : Pᵀ = P) :
    (P * bᵀ + Q * b⁻¹).det ≠ 0 ∧ (P * bᵀ + Q * b⁻¹).det = (P * b + Q).det / (Q * b + P).det := by
  have hQ : Q = 1 - P := by rw [← hPQ]; abel
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  have h2 : b⁻¹ * b = 1 := nonsing_inv_mul _ hb
  generalize b⁻¹ = c at h1 h2 ⊢
  have hc' : c * P = P * c := by
    calc c * P = c * P * (b * c) := by rw [h1, Matrix.mul_one]
      _ = c * (P * b) * c := by simp only [Matrix.mul_assoc]
      _ = P * c := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hct : bᵀ * P = P * bᵀ := by
    have := congrArg transpose hc
    rw [transpose_mul, transpose_mul, hs] at this
    exact this.symm
  have hPP' : ∀ y : Matrix (Fin r) (Fin r) ℂ, P * (P * y) = P * y := fun y => by rw [← Matrix.mul_assoc, hPP]
  have e1 : (Q * c + P) * (Q * b + P) = 1 := by
    have : c * (P * b) = P := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    subst hQ
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, h2, this, hc', hPP, hPP']
    abel
  have e2 : (P * c + Q) * (P * b + Q) = 1 := by
    have : c * (P * b) = P := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    subst hQ
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, h2, this, hc', hPP, hPP']
    abel
  have e3 : P * bᵀ + Q * c = (P * b + Q)ᵀ * (Q * c + P) := by
    have : ∀ y : Matrix (Fin r) (Fin r) ℂ, bᵀ * (P * y) = P * (bᵀ * y) := fun y => by
      rw [← Matrix.mul_assoc, hct, Matrix.mul_assoc]
    subst hQ
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, hs,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, this, hct, hPP, hPP']
    abel
  have d1 := congrArg det e1
  have d2 := congrArg det e2
  rw [det_mul, det_one] at d1 d2
  rw [e3, det_mul, det_transpose]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul_eq_one d2) (left_ne_zero_of_mul_eq_one d1), ?_⟩
  rw [div_eq_mul_inv, eq_inv_of_mul_eq_one_left d1]

theorem isUnit_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (h : IsONFr X x) (τ : X.Ψ) : IsUnit (mat x τ).det := by
  have e : FD.gram τ.1 X.Gm (mat x τ) = (mat x τ)ᵀ * (X.Gm.map τ.1 * (mat x τ).map conj) := by
    ext a b
    simp only [FD.gram, hermC, FD.col, of_apply, mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc]
  have d := congrArg det (e.symm.trans (h τ))
  rw [det_mul, det_transpose, sgnM, det_diagonal] at d
  refine isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (d ▸ Finset.prod_ne_zero_iff.2 fun a _ => ?_))
  unfold sgn
  split_ifs <;> simp

def prFst (r p : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => if (a : ℕ) < p then 1 else 0

theorem prFst_block_zero {r p : ℕ} {b : Matrix (Fin r) (Fin r) ℂ} (h : b * prFst r p = prFst r p * b) {a c : Fin r}
    (hac : ¬ ((a : ℕ) < p ↔ (c : ℕ) < p)) : b a c = 0 := by
  have := congrFun (congrFun h a) c
  simp only [prFst, mul_diagonal, diagonal_mul] at this
  by_cases ha : (a : ℕ) < p <;> by_cases hc : (c : ℕ) < p <;> simp_all

theorem perC_block {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x x' : Frame X.Ψ r) (τ : X.Ψ) (b : Matrix (Fin r) (Fin r) ℂ) (hb : IsUnit b.det)
    (hx' : mat x' τ = mat x τ * b) (hc : b * prFst r X.p0 = prFst r X.p0 * b) (u : X.Ψ → Fin r → ℂ) (a : Fin r) :
    perC X x' u (τ, a) = ∑ c, (prFst r X.p0 * bᵀ + (1 - prFst r X.p0) * b⁻¹) a c * perC X x u (τ, c) := by
  have hc' : b⁻¹ * prFst r X.p0 = prFst r X.p0 * b⁻¹ := by
    calc b⁻¹ * prFst r X.p0 = b⁻¹ * prFst r X.p0 * (b * b⁻¹) := by rw [mul_nonsing_inv _ hb, Matrix.mul_one]
      _ = b⁻¹ * (prFst r X.p0 * b) * b⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hc, ← Matrix.mul_assoc, nonsing_inv_mul _ hb, Matrix.one_mul]
  have hN : ∀ c, (prFst r X.p0 * bᵀ + (1 - prFst r X.p0) * b⁻¹) a c = if (a : ℕ) < X.p0 then b c a else b⁻¹ a c := by
    intro c
    simp only [Matrix.sub_mul, Matrix.one_mul, prFst, Matrix.add_apply, Matrix.sub_apply, diagonal_mul, transpose_apply]
    split_ifs <;> simp
  simp only [hN, perC, hx']
  by_cases ha : (a : ℕ) < X.p0
  · simp only [ha, if_true]
    have : hermC τ.1 X.Gm (FD.col (mat x τ * b) a) (u τ) =
        ∑ c, b c a * hermC τ.1 X.Gm (FD.col (mat x τ) c) (u τ) := by
      simp only [hermC, FD.col, mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc0 : (c : ℕ) < X.p0
    · simp only [hc0, if_true]
    · rw [prFst_block_zero hc (by tauto), zero_mul, zero_mul]
  · simp only [ha, if_false]
    rw [Matrix.mul_inv_rev, ← mulVec_mulVec]
    change ∑ c, b⁻¹ a c * _ = _
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc0 : (c : ℕ) < X.p0
    · rw [prFst_block_zero hc' (by tauto), zero_mul, zero_mul]
    · simp only [hc0, if_false]

theorem sgnM_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    sgnM X = (2 : ℂ) • prFst r X.p0 - 1 := by
  ext a c
  by_cases h : a = c
  · subst h
    simp only [sgnM, prFst, sgn, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq]
    split_ifs <;> norm_num
  · simp [sgnM, prFst, h]

theorem block_of_inv {r : ℕ} (P x k s : Matrix (Fin r) (Fin r) ℂ) (hx : IsUnit x.det)
    (h1 : s * x = -(x * ((2 : ℂ) • P - 1))) (h2 : s * (k * x) = -(k * x * ((2 : ℂ) • P - 1))) :
    (x⁻¹ * (k * x)) * P = P * (x⁻¹ * (k * x)) ∧
      ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det = (P * (x⁻¹ * (k * x)) + (1 - P)).det ∧
      ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det = ((1 - P) * (x⁻¹ * (k * x)) + P).det := by
  have i1 : x * x⁻¹ = 1 := mul_nonsing_inv _ hx
  have i2 : x⁻¹ * x = 1 := nonsing_inv_mul _ hx
  generalize x⁻¹ = y at i1 i2 ⊢
  have i2' : ∀ z : Matrix (Fin r) (Fin r) ℂ, y * (x * z) = z := fun z => by rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  have hs : s = 1 - (2 : ℂ) • (x * (P * y)) := by
    calc s = s * x * y := by rw [Matrix.mul_assoc, i1, Matrix.mul_one]
      _ = _ := by
        rw [h1]
        simp only [Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.mul_assoc, i1, neg_sub]
  have hconj : ∀ A : Matrix (Fin r) (Fin r) ℂ, A.det = (y * (A * x)).det := by
    intro A
    rw [det_mul, det_mul, mul_comm A.det, ← mul_assoc, ← det_mul, i2, det_one, one_mul]
  have a1 : (1 / 2 : ℂ) • (1 - s) = x * (P * y) := by rw [hs]; module
  have a2 : (1 / 2 : ℂ) • (1 + s) = 1 - x * (P * y) := by rw [hs]; module
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun z => y * z) h2
    simp only [hs, Matrix.mul_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', neg_sub, sub_right_inj] at this
    simpa only [Matrix.mul_assoc] using (smul_right_injective _ (two_ne_zero (α := ℂ)) this).symm
  · rw [a1, a2, hconj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', i2]
  · rw [a1, a2, hconj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', i2]

theorem reads_two_frames : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x x' : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsONFr X x' → IsInvOf W hr X x s → IsInvOf W hr X x' s → ∀ k : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → mat x' τ = Matrix.reindex (finCongr hr) (finCongr hr) (k ρ) * mat x τ) → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f ((∏ ρ, (((1 / 2 : ℂ) • (1 - s ρ) * k ρ + (1 / 2 : ℂ) • (1 + s ρ)).det / ((1 / 2 : ℂ) • (1 + s ρ) * k ρ + (1 / 2 : ℂ) • (1 - s ρ)).det) ^ (V.rank / 2)) • φ) x' := by
  intro D ψ θ V W r g hr X bas idx _ _ _ _ hmod _ x x' s hx hx' hs hs' k hk f φ hf
  subst hr
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))
  let t : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hmod.psi _).2 ⟨ρ, rfl⟩⟩
  have ht : Function.Bijective t := ⟨fun a b h => hinj (congrArg Subtype.val h), fun τ => by
    obtain ⟨ρ, h⟩ := (hmod.psi τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext h.symm⟩⟩
  have hu := isUnit_det_of_isONFr X x hx
  have hu' := isUnit_det_of_isONFr X x' hx'
  let b : X.Ψ → Matrix (Fin W.rank) (Fin W.rank) ℂ := fun τ => (mat x τ)⁻¹ * mat x' τ
  have hb : ∀ τ, IsUnit (b τ).det := fun τ => by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (hu τ)).mul (hu' τ)
  have hxb : ∀ τ, mat x' τ = mat x τ * b τ := fun τ => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  set P := prFst W.rank X.p0 with hP
  have key : ∀ ρ, b (t ρ) * P = P * b (t ρ) ∧
      ((1 / 2 : ℂ) • (1 - s ρ) * k ρ + (1 / 2 : ℂ) • (1 + s ρ)).det = (P * b (t ρ) + (1 - P)).det ∧
      ((1 / 2 : ℂ) • (1 + s ρ) * k ρ + (1 / 2 : ℂ) • (1 - s ρ)).det = ((1 - P) * b (t ρ) + P).det := by
    intro ρ
    have e0 : mat x' (t ρ) = k ρ * mat x (t ρ) := hk ρ (t ρ) rfl
    have e1 : s ρ * mat x (t ρ) = -(mat x (t ρ) * sgnM X) := hs ρ (t ρ) rfl
    have e2 : s ρ * mat x' (t ρ) = -(mat x' (t ρ) * sgnM X) := hs' ρ (t ρ) rfl
    rw [sgnM_eq] at e1 e2
    rw [e0] at e2
    have := block_of_inv P _ _ _ (hu _) e1 e2
    rw [← e0] at this
    exact this
  have hc : ∀ τ, b τ * P = P * b τ := fun τ => by
    obtain ⟨ρ, rfl⟩ := ht.2 τ
    exact (key ρ).1
  let N : X.Ψ → Matrix (Fin W.rank) (Fin W.rank) ℂ := fun τ => P * (b τ)ᵀ + (1 - P) * (b τ)⁻¹
  have hN : ∀ τ, (N τ).det ≠ 0 ∧ (N τ).det = (P * b τ + (1 - P)).det / ((1 - P) * b τ + P).det := fun τ =>
    det_tr_inv_block P (1 - P) (b τ) (hb τ) (by abel) (by
      rw [hP, prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp) (hc τ) (by
      rw [hP, prFst, diagonal_transpose])
  let e : Fin g ≃ Fin W.rank × X.Ψ := idx.trans (Equiv.prodComm _ _)
  have hdet : ((blockDiagonal N).submatrix e e).det = ∏ τ, (N τ).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal]
  have main := reads_of_perC θ V W rfl X bas idx x x' ((blockDiagonal N).submatrix e e)
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (hN τ).1)) (fun u => by
      funext j
      have h1 : ((blockDiagonal N).submatrix e e *ᵥ fun j => perC X x u (idx j)) j =
          ∑ p : Fin W.rank × X.Ψ, blockDiagonal N (e j) p * perC X x u p.swap := by
        rw [← e.sum_comp]
        rfl
      rw [h1, Fintype.sum_prod_type]
      refine (perC_block X x x' (idx j).1 (b _) (hb _) (hxb _) (hc _) u (idx j).2).trans ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single (idx j).1]
      · exact congrArg (· * _) (blockDiagonal_apply_eq N (idx j).2 c (idx j).1).symm
      · intro τ _ hτ
        have : blockDiagonal N (e j) (c, τ) = 0 := blockDiagonal_apply_ne N (idx j).2 c hτ.symm
        rw [this, zero_mul]
      · simp) f φ hf
  convert main using 2
  rw [hdet, Finset.prod_pow, ← ht.prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [(hN _).2, (key ρ).2.1, (key ρ).2.2]

end

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMapCoeffSpaceOfJetStepPartitionTriplesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetMap_coeffSpace_of_jetStepPartitionTriples : ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (a b : ℕ), a < b → ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
  first | exact @GlobalTheory.ColNorms.jetInVV_of_stepWeights | exact GlobalTheory.ColNorms.jetInVV_of_stepWeights | (intros; apply GlobalTheory.ColNorms.jetInVV_of_stepWeights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetOperatorBound_at_embedding_of_complexOpNormSq : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  first | exact @GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | exact GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | (intros; apply GlobalTheory.coefOpLe_jetOp_of_opNormSqLe <;> assumption)
end

