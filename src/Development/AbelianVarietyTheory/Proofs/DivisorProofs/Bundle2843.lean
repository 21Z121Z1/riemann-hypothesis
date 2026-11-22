import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullDegIdOfCommonFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_pullDeg_id_of_common_fieldExtension : ∀ (K Ω : Type) [Field K] [Field Ω] (l : K →+* Ω) (D₁ D₂ : DegPre K) (D : DegPre Ω) (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) (φ : D₂.P.A ≅ D₁.P.A), IsMonHom φ.hom → h₂.e.hom.left ≫ pullback.fst D₂.P.A.hom (specOf l) ≫ φ.hom.left = h₁.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf l) → Nonempty (IsPullDeg (RingHom.id K) D₁ D₂) := by
  first | exact @GlobalTheory.nonempty_isPullDeg_id_of_common_pull | exact GlobalTheory.nonempty_isPullDeg_id_of_common_pull | (intros; apply GlobalTheory.nonempty_isPullDeg_id_of_common_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumMult

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

abbrev multW (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (e : ℕ)
    (i i' : Fin 1 → U.LG.L.ι) : (thickObj R (maximalIdeal R) e G).left.Opens :=
  ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
    (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'

def MultAct (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (N : ℕ)
    (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, multW U b e i i')) :
    Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ (f : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), (∀ e, U.ExpandsAt e k s f.f) →
    ∃ F : IntFam (maximalIdeal R) D.toPre (N * k), ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι),
      ChartExpOn U.toUnifPre e (N * k) i' (multW U b e i i')
        (m e i i' ^ k * ((thickObj R (maximalIdeal R) e G).left.presheaf.map
          (homOfLE (inf_le_left : multW U b e i i' ≤
            ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom
          ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) F.f

def LeadPt (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G)
    (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, multW U b e i i')) :
    Prop :=
  ∃ x : D.toPre.P.A.left, D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧
    ∀ y : (thickObj R (maximalIdeal R) 0 G).left, (U.gt 0).pG.left y = x →
      ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ multW U b 0 i i' →
        y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i')

def PosN (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) :
    Prop :=
  RelAmple D.toPre.P.A (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) ∧
    ∀ (κ : D.toPre.X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 →
      (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) →
      (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) →
      (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
        algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) →
      ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y)

def NonzeroAt (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (N : ℕ)
    (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]))
    (x : D.toPre.P.A.left) : Prop :=
  ∀ j : Fin 2 → D.toPre.P.L.ι,
    x ∈ LB.wchart D.toPre.P.L (![𝟙 D.toPre.P.A.left, a.left] : Fin 2 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) j →
      x ∈ D.toPre.P.A.left.basicOpen (σ₀.f j)

end GlobalTheory.MumMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y}

theorem norms_zp {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (m : ℤ) :
    Norms V (ArInt.zp L m) (fun x => f x ^ m) (fun σ y => m * a σ y) (fun v e y => m * l v e y) := by
  have h₁ := GlobalTheory.T.norms_tensor_power F Y V L f a l m.toNat h
  have h₂ := GlobalTheory.T.norms_dual_bundle F Y V _ _ _ _ (GlobalTheory.T.norms_tensor_power F Y V L f a l (-m).toNat h)
  refine (GlobalTheory.T.norms_tensor_product F Y V _ _ _ _ _ _ _ _ h₁ h₂).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · rcases m with n | n
    · simp
    · rw [zpow_negSucc]
      have : (Int.negSucc n).toNat = 0 := rfl
      have h' : (-Int.negSucc n).toNat = n + 1 := rfl
      rw [this, h', pow_zero, one_mul]
  · have := Int.toNat_sub_toNat_neg m
    have hE : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = m := by exact_mod_cast this
    linear_combination a σ y * hE
  · have := Int.toNat_sub_toNat_neg m
    have hE : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = m := by exact_mod_cast this
    linear_combination l v e y * hE

theorem norms_comb {ι : Type} [Fintype ι] {L : ι → HermLB V.p} {f : ι → Y.X → Y.Fn} {a : ι → ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ι → ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : ∀ i, Norms V (L i) (f i) (a i) (l i)) (n : ι → ℤ) :
    Norms V (ArInt.comb L n) (fun x => ∏ i, f i x ^ n i) (fun σ y => ∑ i, (n i : ℝ) * a i σ y)
      (fun v e y => ∑ i, (n i : ℝ) * l i v e y) := by
  have key : ∀ s : List ι, Norms V (s.foldr (fun i M => (ArInt.zp (L i) (n i)).tens M) (HermLB.triv V.p))
      (fun x => (s.map fun i => f i x ^ n i).prod) (fun σ y => (s.map fun i => (n i : ℝ) * a i σ y).sum)
      (fun v e y => (s.map fun i => (n i : ℝ) * l i v e y).sum) := by
    intro s
    induction s with
    | nil => exact (GlobalTheory.T.conjugate_weight_smooth_normalization F Y V).1
    | cons i s ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, List.sum_cons]
      exact GlobalTheory.T.norms_tensor_product F Y V _ _ _ _ _ _ _ _ (norms_zp (h i) (n i)) ih
  refine (key Finset.univ.toList).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · exact Finset.prod_map_toList _ _
  · exact Finset.sum_map_toList _ _
  · exact Finset.sum_map_toList _ _

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulEqZeroOfRadical
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSSymm

theorem exists_leftInverse {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {g : ℕ}
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [hf : IsMonHom f] {m : ℕ} (hm : 0 < m)
    (hker : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1) :
    ∃ h : B ⟶ A, IsMonHom h ∧ f ≫ h = 𝟙 A ^ m := by
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have := hA.comm
  have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B f hf inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hm
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ m = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ m = 1} => z.1) e)
  have hflat : Flat f.left :=
    SemiAbMulFlat.flat_of_flatOver_fields f.left B.hom inferInstance
      (by rw [Over.w]; infer_instance) (by rw [Over.w]; infer_instance) inferInstance
      fun k _ s => FibreFlat.flatOver_of_pullback f s (IsogenyQuasiInverse.flat_fibre A B g hA hB hAg hBg f k s)
  have hsurj : Surjective f.left :=
    AbLaw.MulN.surjective_of_geomFibres f fun K _ _ t =>
      (IsogenyQuasiInverse.flat_surjective_geomFibre A B g hA hB hAg hBg f K t).2
  have hmA : IsMonHom (𝟙 A ^ m) := AbLaw.MulN.isMonHom_mulA A m
  exact (exists_monHom_factor_of_flat_surjective _ A B A f (𝟙 A ^ m) hf hmA
    hflat hsurj inferInstance fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hker T x hx]).1

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R))

theorem additive [IsTotallyReal F] (c : 𝔠.elt) : IsAdditive (X.P c) ∧ IsAdditive (swap (X.P c)) := by
  obtain ⟨c₁, hc₁⟩ := fracId_exists_totPos F 𝔠
  have hL := pull_isLB (X.isLB c₁) (lift (𝟙 X.A) (𝟙 X.A)).left
  obtain ⟨H, hH, hamp⟩ := BirigidLift.exists_relAmple_prod X.ab X.ab hL (X.pos c₁ hc₁) hL (X.pos c₁ hc₁)
  exact BirigidLift.additive_of_triv X.ab X.ab hH hamp (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem cupSquare (HR : AbelianDeRham) : CupSquare (dp0 R) (𝟙 _) (X.A ⊗ X.A) :=
  cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)

variable {X}

theorem nsmul_eq_zero_of_radical [IsTotallyReal F] (HR : AbelianDeRham) (HD : DualAbelianScheme) {c : 𝔠.elt} {m : ℕ}
    (hm0 : 0 < m) (hm : ∀ d : 𝔠.elt, ∃ t : 𝓞 F, (m : 𝓞 F) • d = t • c) {ψ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hψ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) ψ) {y : HdR X.A} (hy : ∀ x, ψ x y = 0) : m • y = 0 := by
  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD (Sp R) X.A X.ab
  have hBg := hBg _ X.dim
  obtain ⟨a₁, a₂⟩ := additive X c
  obtain ⟨lam, hlam, hcls⟩ := BirigidLift.exists_hom hd hd'.additive (X.isLB c) a₁ a₂
  have hker : ∀ (T : Over (Sp R)) (x : T ⟶ X.A), x ≫ lam = 1 → x ^ m = 1 := by
    intro T x hx
    have tr : Triv (ev (X.P c) (fst X.A T) (snd X.A T ≫ x)) := by
      rw [triv_ev_iff (X.isLB c), BirigidLift.evc_of_cls hd.isLB (X.isLB c) hcls, Category.assoc, hx, comp_one]
      exact evc_one_right hd.isLB hd.zero _
    have k := X.ker c T x tr (m : 𝓞 F) hm
    rwa [PolPrimeTo.act_natCast, comp_pow, Category.comp_id] at k
  obtain ⟨μ', hμ', e₁⟩ := exists_leftInverse X.ab hB X.dim hBg lam hm0 hker
  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := AbelianDualCrystal.duality HR X.ab X.dim hB hBg (hd.isPerfect hd')
  have e : LBIso (ev Q (fst X.A X.A) (snd X.A X.A ≫ lam)) (ev (X.P c) (fst X.A X.A ≫ 𝟙 X.A) (snd X.A X.A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB (X.isLB c) _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev (X.isLB c), BirigidLift.evc_of_cls hd.isLB (X.isLB c) hcls, Category.comp_id]
  have z : push (dp0 R) (𝟙 _) lam y = 0 := (injective_iff_map_eq_zero _).1 (hperf φ hφ).1.bijective_right.1 _ <|
    LinearMap.ext fun x ↦ by
      have k := IsCorrForm.adjoint (cupSquare X HR) hd.isLB (X.isLB c) hφ hψ (𝟙 X.A) lam e x y
      rw [push_id] at k
      exact k.trans (hy _)
  haveI := PolPrimeTo.isMonHom_id_pow X.A m
  have k := push_push (κ := dp0 R) (t := 𝟙 _) lam μ' _ e₁ y
  rw [z, map_zero, PolPrimeTo.push_id_pow] at k
  rw [← Nat.cast_smul_eq_nsmul R]
  exact k.symm

theorem form_smul (HR : AbelianDeRham) {c d : 𝔠.elt} {b : 𝓞 F} (e : d = b • c)
    {φ χ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ)
    (hχ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P d) χ) (x y : HdR X.A) :
    χ x y = φ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  subst e
  have := X.rm.hom
  obtain ⟨χ', hχ', k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (homMor (dp0 R) (𝟙 _) (X.rm.act b)) (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)).left)
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (X.isLB (b • c)) (LBIso.symm (X.smul b c))
  obtain rfl := hχ.unique (cupSquare X HR) (X.isLB (b • c)) hχ'
  have e := k (push (dp0 R) (𝟙 _) (𝟙 X.A) x) x (push (dp0 R) (𝟙 _) (X.rm.act b) y) y (fun _ ↦ rfl) fun _ ↦ rfl
  rwa [push_id, LinearMap.id_apply, RingHom.id_apply] at e

variable (X) in

theorem exists_form_of (HR : AbelianDeRham) (c : 𝔠.elt) : ∃ φ, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ :=
  exists_isCorrForm (cupSquare X HR) (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem form_skew (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (x y : HdR X.A) : φ x y = -φ y x :=
  JetIsotropic.corrForm_antisymm (cupSquare X HR) (X.isLB c) (X.symm c) hφ x y

theorem form_balanced (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (s : R ⊗[ℤ] 𝓞 F) (x y : HdR X.A) :
    φ (actAlg (dp0 R) (𝟙 _) X.rm s x) y = φ x (actAlg (dp0 R) (𝟙 _) X.rm s y) := by
  induction s with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul r b =>
    obtain ⟨χ, hχ⟩ := exists_form_of X HR (b • c)
    rw [actAlg_tmul, actAlg_tmul, map_smul, map_smul, LinearMap.smul_apply, form_skew HR hφ,
      ← form_smul HR rfl hφ hχ, ← form_smul HR rfl hφ hχ, form_skew HR hχ x]

theorem form_fil (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) : ∀ a ∈ Fil X.A, ∀ b ∈ Fil X.A, φ a b = 0 := by
  intro a ha b hb
  obtain ⟨ψ, hψ, eψ⟩ := hφ.isPolForm
  have t := (HR.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim) _
    (X.isLB c) ψ hψ).1 _ (push_mem_Fil (inl X.A X.A) ha) _ (push_mem_Fil (inr X.A X.A) hb)
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one] at t
  simpa using t

theorem form_symm [IsTotallyReal F] (HR : AbelianDeRham) (HD : DualAbelianScheme) (hX : X.IsRapoport)
    (hL : LieExact X.A) {κ : Fil X.A →ₗ[R] X.Lie} (hκ : X.IsLinearKS κ) {c : 𝔠.elt}
    {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) {f f' : Fil X.A}
    {k k' : HdR X.A} (hk : hL.toLie X.rm k = κ f) (hk' : hL.toLie X.rm k' = κ f') : φ f k' = φ f' k := by
  letI := X.lieModule
  haveI : Module.Invertible (R ⊗[ℤ] 𝓞 F) X.Lie := hX
  have sm : ∀ (r : R) (b : 𝓞 F) (v : X.Lie), (r ⊗ₜ[ℤ] b : R ⊗[ℤ] 𝓞 F) • v = r • b • v := fun _ _ _ ↦ rfl
  haveI : IsScalarTower R (R ⊗[ℤ] 𝓞 F) X.Lie := ⟨fun r s v ↦ by
    induction s with
    | zero => simp
    | add a b ha hb => simp only [smul_add, add_smul, ha, hb]
    | tmul r' b => rw [smul_tmul', sm, sm, smul_assoc]⟩
  have lie : ∀ (s : R ⊗[ℤ] 𝓞 F) x, hL.toLie X.rm (actAlg (dp0 R) (𝟙 _) X.rm s x) = s • hL.toLie X.rm x :=
    fun s x ↦ by
    induction s with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
    | tmul r b => rw [actAlg_tmul, map_smul, hL.toLie_act, sm]
  have mem : ∀ (s : R ⊗[ℤ] 𝓞 F) (x : Fil X.A), actAlg (dp0 R) (𝟙 _) X.rm s x ∈ Fil X.A := fun s x ↦ by
    have : hL.toLie X.rm x = 0 := LinearMap.mem_ker.1 ((hL.ker_toLie X.rm).ge x.2)
    refine (hL.ker_toLie X.rm).le (LinearMap.mem_ker.2 ?_)
    rw [lie, this, smul_zero]
  let ρ : R ⊗[ℤ] 𝓞 F → Fil X.A → Fil X.A := fun s x ↦ ⟨_, mem s x⟩
  have hρ : ∀ s x, κ (ρ s x) = s • κ x := fun s x ↦ by
    induction s with
    | zero => rw [zero_smul, ← map_zero κ]; exact congrArg κ (Subtype.ext (by simp [ρ]))
    | add a b ha hb =>
      rw [add_smul, ← ha, ← hb, ← map_add]
      exact congrArg κ (Subtype.ext (by simp [ρ]))
    | tmul r b =>
      rw [sm, ← hκ b x (ρ (1 ⊗ₜ b) x) ((actAlg_tmul _ _ _ _ _ _).trans (one_smul _ _)), ← map_smul]
      exact congrArg κ (Subtype.ext (by simp [ρ, actAlg_tmul]))
  refine sub_eq_zero.1 (eq_zero_of_coprime fun l hl ↦ ?_)
  haveI := Fact.mk hl
  obtain ⟨c₀, -, hgen⟩ := FracGen.exists_gen F 𝔠 l
  obtain ⟨m, hm0, hml, hm⟩ := PolPrimeTo.exists_uniform 𝔠 l c₀ hgen
  obtain ⟨n, e, t, τ, hn, cas, tr⟩ := exists_casimir F l R
  obtain ⟨φ₀, hφ₀⟩ := exists_form_of X HR c₀
  obtain ⟨b, hb⟩ := hm c
  obtain ⟨χ, hχ⟩ := exists_form_of X HR ((m : 𝓞 F) • c)
  have eφ : ∀ x y, m • φ x y = φ₀ x (actAlg (dp0 R) (𝟙 _) X.rm (1 ⊗ₜ b) y) := fun x y ↦ by
    rw [actAlg_tmul, one_smul, ← form_smul HR hb hφ₀ hχ, form_smul HR rfl hφ hχ, map_natCast, Module.End.natCast_apply,
      map_nsmul]
  have key := symm_of_casimir e t τ n m cas tr ρ (hL.filToDual X.rm φ₀ (form_fil HR hφ₀))
    (fun s x v ↦ by
      obtain ⟨y, rfl⟩ := hL.toLie_surjective X.rm v
      rw [← lie, hL.filToDual_toLie, hL.filToDual_toLie]
      exact form_balanced HR hφ₀ s x y)
    (fun x hx ↦ Subtype.ext (nsmul_eq_zero_of_radical HR HD hm0 hm hφ₀ fun y ↦ by
      rw [form_skew HR hφ₀, ← hL.filToDual_toLie X.rm φ₀ (form_fil HR hφ₀), hx, LinearMap.zero_apply, neg_zero]))
    κ hρ f (ρ (1 ⊗ₜ b) f')
  rw [hρ, ← hk, ← hk', ← lie, hL.filToDual_toLie, hL.filToDual_toLie, form_balanced HR hφ₀, ← eφ, ← eφ, ← smul_sub,
    ← mul_smul] at key
  exact ⟨_, ((hml.mul_left hn).mul_left hn).mul_left hml, key⟩

end GlobalTheory.KSSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NzEverywhere
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem nz_everywhere {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] (L : LB G.left) {R : Type} [CommRing R]
    [IsLocalRing R] (χ : Sp R ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) (h : NZ G L χ σ) :
    ∀ y : (Over.mk χ).left, ∃ g, (fst (Over.mk χ) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨x, hc, hx⟩ := h
  haveI : Smooth (fst (Over.mk χ) G).left := by
    change Smooth (pullback.fst χ G.hom)
    infer_instance
  have ho : IsOpen ((fst (Over.mk χ) G).left '' (nonzeroLocus σ : Set _)) :=
    (fst (Over.mk χ) G).left.isOpenMap _ (nonzeroLocus σ).isOpen
  intro y
  obtain ⟨g, hg, e⟩ := (IsLocalRing.specializes_closedPoint (R := R) y).mem_open ho ⟨x, hx, hc⟩
  exact ⟨g, e, hg⟩

theorem nz_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G →
    ∀ (R V : Type) [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (χ : Sp R ⟶ S) (σ : SecAt G L χ)
      (φ : R →+* V), NZ G L χ σ → NZ G L (spMap φ ≫ χ) (SecAt.pull G L σ φ) := by
  intro S G _ L hL hG R V _ _ _ _ χ σ φ h
  haveI : Smooth G.hom := hG.smooth
  exact nz_pullS G hL σ (nz_everywhere G L χ σ h) (spMap φ ≫ χ) _

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

open AdjComp in

theorem Adj.of_twisted_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  intro R _ _ Q₁ Q₂ a a₁ a₁' a' h h₁ h₁' h' ma ma' ca ca' H₁ H₂
  obtain ⟨mb, mb', cb, cb', w₁, g₁, V₁⟩ := H₁
  obtain ⟨w₂, g₂, V₂⟩ := H₂
  let m₂ : Q₁.B ⊗ Q₂.B ⟶ Q₁.B ⊗ Q₁.B := lift (fst _ _) (snd _ _ ≫ a')
  have xB : ∀ i, (![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B ≫ a₁, snd Q₁.B Q₁.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B, snd Q₁.B Q₁.B ≫ a₁'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cB := cubePull Q₁.M.L m₂ _ _ xB
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lB : (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC w₂ g₂ (pullIso cB cC w₁) (pullIso_isGen cB cC g₁)
  refine ⟨ma, inferInstance, ca, fun y => ?_, w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb', ca', Category.assoc]
  · have e₂ := V₂ y y' z J₁ J₂ hJ₁ hJ₂
    have e₁ := V₁ y (h' y') z J₁ J₁ hJ₁ hJ₁
    have hP : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₁.c (h' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, ca', Category.assoc]
    rw [hP] at e₁
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left = P at e₂ e₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] I.down).left) P
    have mB := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] I.down).left) P
    have mA := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left) P
    have K : adjVal w P z J₁ J₂ = adjVal w₂ P z J₁ J₂ * adjVal w₁ (P ≫ m₂.left) z J₁ J₁ := by
      refine ((adjVal_of w P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB cC w₁ P z (_, _) ⟨mC, mB⟩) rfl))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂ P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).symm
        (adjVal_of w₁ (P ≫ m₂.left) z J₁ J₁ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB I]
    rw [AddMonoidHom.comp_apply, e₂, e₁, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheafStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Nonempty (Model s (GlobalTheory.AbLaw.cechLB s (LB.triv X) D)) := by
  first | exact @GlobalTheory.CechPoset.model_cechLB | exact GlobalTheory.CechPoset.model_cechLB | (intros; apply GlobalTheory.CechPoset.model_cechLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

def OrigVal {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {k : ℕ} {α : D.X} (b : D.SecB k α) (v : R) : Prop :=
  ∀ (z : Sp R) (J : (Sp R ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    sval b (unitW D.P.A) z J = stalkOf z v * (val D.rig (idW R) z J).val ^ k

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupCocycleMemCobRangeOfDiagonalSumZeroStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_cocycle_mem_cob_range_of_diagonalSum_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 → z ∈ LinearMap.range G.cob := by
  first | exact @GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero | exact GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero | (intros; apply GlobalTheory.PtExt.cocycle_mem_range_cob_of_diagSum_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleFormsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  first | exact @GlobalTheory.PDForm.quot_fil_rel | exact GlobalTheory.PDForm.quot_fil_rel | (intros; apply GlobalTheory.PDForm.quot_fil_rel <;> assumption)
end

