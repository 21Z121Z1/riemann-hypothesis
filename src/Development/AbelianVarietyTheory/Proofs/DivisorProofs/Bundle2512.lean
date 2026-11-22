import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainSectionsQuotMaximalIdealSmoothConnectedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_sections_quot_maximalIdeal_smooth_connected : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom → GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U, G.hom y = closedPoint R → IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  first | exact @GlobalTheory.isDomain_quot_maximalIdeal_of_smooth | exact GlobalTheory.isDomain_quot_maximalIdeal_of_smooth | (intros; apply GlobalTheory.isDomain_quot_maximalIdeal_of_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrict
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isDominant_of_isIso_restrict (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    (U : X.Opens) (hU : (U : Set X).Nonempty) (h : IsIso (s ∣_ U)) : IsDominant s := by
  refine ⟨?_⟩
  have hd : Dense (U : Set X) := U.isOpen.dense hU
  refine hd.mono ?_
  intro x hx
  obtain ⟨y, hy⟩ := (s ∣_ U).surjective ⟨x, hx⟩
  refine ⟨y.1, ?_⟩
  have := morphismRestrict_base_coe s U y
  rw [hy] at this
  exact this.symm

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

def e8 (W : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ := W + W.transpose

def actMat (W : Matrix (Fin 8) (Fin 8) ℤ) : Fin 2 → Matrix (Fin 8) (Fin 8) ℤ :=
  ![(e8 W).adjugate * W, (e8 W).adjugate * W.transpose]

variable {S : Scheme.{0}}

def IsProd {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)) : Prop :=
  (∀ a, IsMonHom (pr a)) ∧ ∀ (T : Over S) (y : Fin 8 → (T ⟶ B)), ∃! x : T ⟶ A, ∀ a, x ≫ pr a = y a

def IsE8WeightedBundle (W : Matrix (Fin 8) (Fin 8) ℤ) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B))
    (L : LB A.left) (M : LB B.left) : Prop :=
  LBIso L (LB.LinComb M (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)))

def IsPPFib (B : Over S) [GrpObj B] (g : ℕ) (M : RigLB B) : Prop :=
  IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ Nonempty (CubicalStr B M) ∧ RelAmple B M.L ∧ KTriv B M.L

def ActsBy {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (f : A ⟶ A)
    (m : Matrix (Fin 8) (Fin 8) ℤ) : Prop :=
  ∀ a, f ≫ pr a = ∏ b, pr b ^ m a b

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenOfIsTopFormFrame
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameEtale

theorem etale_eval₂Hom_of_basis {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (hα : α.Smooth)
    {n : ℕ} (z : Fin n → A) (b : Module.Basis (Fin n) A (Omega α)) (hb : ∀ i, b i = dFun α (z i)) :
    (MvPolynomial.eval₂Hom α z).Etale := by
  letI := α.toAlgebra
  haveI : Algebra.Smooth k A := hα
  letI := (MvPolynomial.eval₂Hom α z).toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C α z r).symm
  have hX (i) : algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i) = z i :=
    MvPolynomial.eval₂Hom_X' α z i
  exact EtaleCoordJacobian.etale_of_basis k A (Fin n) b fun i => by rw [hX]; exact hb i

theorem isEtCoord_of_isFrame : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (V : Y.Opens) (z : Fin n → Γ(Y, V)), IsFrame (dOn q z) → IsAffineOpen V ∧ IsEtCoord q V z := by
  intro k _ Y q n hq V z hz
  refine ⟨hz.affine, ?_⟩
  obtain ⟨b, hb⟩ := FrameBasis.exists_basis_of_isFrame k Y q n hq V z hz
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have h := HasRingHomProperty.appLE (@Smooth) q inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hz.affine⟩ le_top
  have h₁ : (DVR.FlatBC.algX q V).Smooth :=
    RingHom.Smooth.respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv h
  exact etale_eval₂Hom_of_basis (DVR.FlatBC.algX q V) h₁ z b hb

end GlobalTheory.FrameEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo

namespace GlobalTheory.ChernWeilLine

variable {F : Type} [Field F] {X : Var F} {ι : Type} [Finite ι]

def ofDivisors (Δ : ι → X.Dv) : Fr (ratOf X) (fun _ : ι => 1) 0 where
  S z := {A | ∀ i, (Δ i).GeneratesAt z (A i 0 0)}
  loc z := by
    have := Fintype.ofFinite ι
    choose U hz g hg using fun i => (Δ i).exists_isEqn_nhds z
    let W : X.X.Opens := ⨅ i, U i
    have hW : z ∈ W := by
      show z ∈ ((⨅ i, U i : X.X.Opens) : Set X.X)
      rw [TopologicalSpace.Opens.coe_iInf]; exact Set.mem_iInter.2 hz
    refine ⟨W, fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹, hW, fun _ => by simp, fun z' hz' A => ?_⟩
    have hz'' (i : ι) : z' ∈ U i := by
      have : z' ∈ ((⨅ i, U i : X.X.Opens) : Set X.X) := hz'
      rw [TopologicalSpace.Opens.coe_iInf] at this; exact Set.mem_iInter.1 this i
    have e (i : ι) (a b : Fin 1) : (A * (fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹ :
        Mat (fun _ : ι => 1) X.Fn)⁻¹) i a b = A i 0 0 * g i := by
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.mul_apply, Matrix.inv_def]
    refine ⟨fun h i => ?_, fun h i => ?_⟩
    · have h' := ((hg i z' (hz'' i)).generatesAt_iff).1 (h i)
      refine ⟨fun a b => ?_, ?_, ?_, fun a b ha => absurd ha (by simp)⟩
      · rw [e]; exact mem_O_ratOf.2 h'.regAt
      · rw [Matrix.det_unique, e]; exact h'.ne_zero
      · rw [Matrix.det_unique, e]; exact mem_O_ratOf.2 h'.inv.regAt
    · obtain ⟨h1, h2, h3, -⟩ := h i
      rw [Matrix.det_unique, e] at h2 h3
      exact ((hg i z' (hz'' i)).generatesAt_iff).2
        ((unitAt_iff h2).2 ⟨mem_O_ratOf.1 (e i 0 0 ▸ h1 0 0), mem_O_ratOf.1 h3⟩)

theorem isGraded_ofDivisors (Δ : ι → X.Dv) : IsGraded (lineFlag (ofDivisors Δ)) fun x => Δ x.1 := by
  refine ⟨1, fun i => ⟨1, (Δ i).isEqn_genericPoint 1, by simpa using unitAt_one _⟩, fun y x => ?_⟩
  choose g hg using fun i => (Δ i).exists_isEqn y
  refine ⟨fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹,
    fun i => CartierDiv.isEqn_iff_generatesAt_inv.1 (hg i), g x.1, ?_, hg x.1⟩
  obtain ⟨i, a⟩ := x
  rw [Subsingleton.elim a 0]
  simp [Matrix.inv_def]

end GlobalTheory.ChernWeilLine

namespace GlobalTheory.ChernWeilLine

variable {F : Type} [Field F] [NumberField F] {ι : Type}

def lineGram {Y : Var F} {σ : F →+* ℂ} {Δ : ι → Y.Dv} (C : CxSt F) (m : ∀ i, C.Met Y σ (Δ i)) :
    Mat (fun _ : ι => 1) Y.Fn → Pts Y σ → Mat (fun _ : ι => 1) ℂ :=
  fun A y i => Matrix.of fun _ _ => ((C.pn Y σ (Δ i) (m i) (C.cx Y σ (A i 0 0)) y : ℝ) : ℂ)

end GlobalTheory.ChernWeilLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GrpPB

theorem isGrpPullback_comp {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {P : Over T} [GrpObj P] {f : S' ⟶ S} {t : T ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : P.left ⟶ G'.left}
    (h₁ : IsGrpPullback P G' t ψ) (h₂ : IsGrpPullback G' G f φ) :
    IsGrpPullback P G (t ≫ f) (ψ ≫ φ) := by
  refine ⟨h₁.1.paste_horiz h₂.1, fun T₀ x y x₀ y₀ hx hy => ?_⟩
  have wx : ∀ z : T₀ ⟶ P, (z.left ≫ ψ) ≫ G'.hom = (Over.mk (T₀.hom ≫ t)).hom := fun z => by
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w z]; rfl
  let x' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (x.left ≫ ψ) (wx x)
  let y' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (y.left ≫ ψ) (wx y)
  have e₁ : (x' * y').left = (x * y).left ≫ ψ := h₁.2 T₀ x y x' y' rfl rfl
  let e : Over.mk ((Over.mk (T₀.hom ≫ t)).hom ≫ f) ⟶ Over.mk (T₀.hom ≫ t ≫ f) :=
    Over.homMk (𝟙 _) (by simp)
  have e₂ : ((e ≫ x₀) * (e ≫ y₀)).left = (x' * y').left ≫ φ :=
    h₂.2 _ x' y' (e ≫ x₀) (e ≫ y₀) (by simp [e, x', hx]) (by simp [e, y', hy])
  rw [← MonObj.comp_mul, Over.comp_left] at e₂
  simp only [e, Over.homMk_left, Category.id_comp] at e₂
  rw [e₂, e₁, Category.assoc]

theorem baseChange_square {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (t : T ⟶ S') :
    IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧
      ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  have hc := isGrpPullback_comp (isGrpPullback_pullback G' t) h
  refine ⟨hc, ?_⟩
  set P := (Over.pullback t).obj G'
  have w : ∀ q : P ⊗ P ⟶ P, (q.left ≫ pullback.fst G'.hom t ≫ φ) ≫ G.hom = (Over.mk ((P ⊗ P).hom ≫ t ≫ f)).hom :=
    fun q => by
      rw [Category.assoc, Category.assoc, ← Category.assoc _ φ, hc.1.w, ← Category.assoc, Over.w q]; rfl
  let a : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (fst P P))
  let b : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (snd P P))
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]; rfl
  · rw [← Over.comp_left, lift_snd]; rfl

example : ∀ {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ t : T ⟶ S', IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧ ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := @baseChange_square

end GlobalTheory.GrpPB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackTangentCombinationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S0 : Scheme.{0})
    (t : SAB H S0) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (x0 : Sp ℂ_[p] ⟶ S0)
    (ψ' : P.A.A.left ⟶ t.G.left), IsGrpPullback P.A.A t.G x0 ψ' →
    ∀ (m : ℕ) (xs : Fin m → LieG P.Gt) (us : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), (∀ i, LieTie P ψ' (xs i) (us i)) →
      IsCombAtG t x0 us (fun i => algebraMap 𝓞_ℂ_[p] ℂ_[p] (a i)) u → LieTie P ψ' (lieComb P.Gt a xs) u := by
  first | exact @GlobalTheory.FlatModel.lieTie_lieComb | exact GlobalTheory.FlatModel.lieTie_lieComb | (intros; apply GlobalTheory.FlatModel.lieTie_lieComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertEisensteinLatticeValueOfEisensteinSerie
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt eisClass_mk)

namespace GlobalTheory.HilbFam.EisCmp

variable {F : Type} [Field F] [NumberField F]

theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem mem_split (𝔞 𝔟 : Frac F) (v : Fin 2 → F) :
    v ∈ split 𝔞 𝔟 0 ↔ v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 ∈ latM 𝔞 := by
  show v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * 0 ∈ latM 𝔞 ↔ _
  rw [mul_zero, sub_zero]

theorem unit_smul_apply (ε : (𝓞 F)ˣ) (v : Fin 2 → F) (i : Fin 2) : (ε • v) i = ((ε : 𝓞 F) : F) * v i := by
  rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]

def pair (𝔞 𝔟 : Frac F) (q : cls (split 𝔞 𝔟 0)) : LatPair 𝔞 𝔟 :=
  ⟨(q.1.out 1, q.1.out 0), ((mem_split 𝔞 𝔟 _).1 q.2.1).2, ((mem_split 𝔞 𝔟 _).1 q.2.1).1, fun h ↦ q.2.2 (by
    funext i
    fin_cases i
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h)⟩

theorem bij (𝔞 𝔟 : Frac F) :
    Function.Bijective (fun q : cls (split 𝔞 𝔟 0) ↦ Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
  constructor
  · intro q1 q2 h
    obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    refine (Quotient.sound ?_).symm
    refine ⟨ε, ?_⟩
    funext i
    show (ε • q1.1.out) i = _
    rw [unit_smul_apply]
    fin_cases i
    · exact h2.symm
    · exact h1.symm
  · intro cl
    obtain ⟨p, rfl⟩ := Quotient.exists_rep cl
    let v : Fin 2 → F := ![p.1.2, p.1.1]
    have hv : v ∈ split 𝔞 𝔟 0 := (mem_split 𝔞 𝔟 v).2 ⟨p.2.2.1, p.2.1⟩
    have hv0 : v ≠ 0 := fun h ↦ p.2.2.2 (Prod.ext (congrFun h 1) (congrFun h 0))
    obtain ⟨ε, hε⟩ : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out ∈ MulAction.orbit (𝓞 F)ˣ v :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v))
    have hε' : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out = ε • v := hε.symm
    refine ⟨⟨Quotient.mk _ v, ?_, ?_⟩, ?_⟩
    · rw [hε']; exact Submodule.smul_mem _ (ε : 𝓞 F) hv
    · rw [hε']; exact (smul_ne_zero_iff_ne ε).2 hv0
    · refine (Quotient.sound (show (latRel 𝔞 𝔟).r p _ from ⟨ε, ?_, ?_⟩)).symm
      · exact (congrFun hε' 1).trans (unit_smul_apply ε v 1)
      · exact (congrFun hε' 0).trans (unit_smul_apply ε v 0)

theorem term_eq [IsTotallyReal F] (k : ℕ) (σ : ℂ) (w : Emb F → ℂ) (x : Fin 2 → F) :
    gTerm k σ w 1 x = (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
      ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * eisTerm k σ w (x 1, x 0) := by
  have hP : ∏ τ, latPt w (x 1, x 0) τ = (2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * ∏ τ, coord w 1 x τ := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ ↦ ?_
    simp only [latPt, coord, Pi.one_apply]; ring
  have hΛ : (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ Complex.two_pi_I_ne_zero
  unfold gTerm eisTerm
  rw [hP]
  generalize (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F = Λ at hΛ
  have hn : ((‖Λ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hΛ)
  have h1 : Λ ^ k * Λ⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hΛ, one_pow]
  have h2 : ((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ) = 1 := by
    rw [← Complex.cpow_add _ _ hn, show 2 * σ + -2 * σ = 0 by ring, Complex.cpow_zero]
  rw [mul_inv, mul_pow, norm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  generalize (∏ τ, coord w 1 x τ)⁻¹ ^ k = A
  generalize ((‖∏ τ, coord w 1 x τ‖ : ℝ) : ℂ) ^ (-2 * σ) = B
  linear_combination (-(A * B) * (((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ))) * h1 - (A * B) * h2

theorem hasSum_gTerm [IsTotallyReal F] (𝔞 𝔟 : Frac F) {k : ℕ} (hk : Even k) (σ : ℂ) (w : Emb F → ℂ) (S : ℂ)
    (h : HasSum (eisClass 𝔞 𝔟 k σ w) S) :
    HasSum (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out)
      ((((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * S) := by
  have h1 := ((Equiv.hasSum_iff (Equiv.ofBijective _ (bij 𝔞 𝔟))).2 h).mul_left
    (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ))
  have h2 : (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out) = fun q : cls (split 𝔞 𝔟 0) ↦
      (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) *
        eisClass 𝔞 𝔟 k σ w (Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
    funext q
    rw [eisClass_mk 𝔞 𝔟 hk, term_eq]
    rfl
  rw [h2]
  exact h1

theorem isGVal_of_isEis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ)
    (w : Emb F → ℂ), Even k → IsEis 𝔞 𝔟 k G → w ∈ upperHalf F →
    IsGVal k (split 𝔞 𝔟 0) w 1 (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k * G w) := by
  intro F _ _ _ k 𝔞 𝔟 G w hk hG hw
  constructor
  · intro h2
    have h := hasSum_gTerm 𝔞 𝔟 hk 0 w _ (hG.1 h2 w hw)
    rwa [mul_zero, Complex.cpow_zero, mul_one] at h
  · rintro rfl
    obtain ⟨H, hH, rfl⟩ := hG.2 rfl
    have hn : ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (pow_ne_zero _ Complex.two_pi_I_ne_zero))
    refine ⟨fun σ ↦ (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * H σ w, ?_, ?_, ?_⟩
    · have hHd : DifferentiableOn ℂ (fun σ ↦ H σ w) {σ : ℂ | -1 / 2 < σ.re} := hH.2.2 [] w hw
      have hAd : Differentiable ℂ fun σ : ℂ ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
          ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ) := fun σ ↦
        (differentiableAt_const _).mul (((differentiableAt_const (2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn))
      exact hAd.differentiableOn.mul hHd
    · intro σ hσ
      obtain ⟨hsm, hHe⟩ := hH.1 σ hσ w hw
      exact hasSum_gTerm 𝔞 𝔟 hk σ w _ (by rw [hHe]; exact hsm.hasSum)
    · simp only [mul_zero, Complex.cpow_zero, mul_one]

end GlobalTheory.HilbFam.EisCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegral
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam

theorem isIntegral_coord_of_isIntegral (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ)
    (x : Fin 2 → FR E) (_hD : 0 < D) (hθ : IsIntegral ℤ θ)
    (hr : (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E))
    (hu : IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E))) (j : Fin 2) :
    IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  have hc : ∀ y : E, IsIntegral ℤ y → IsIntegral ℤ (IsCMField.complexConj E y) := fun y hy =>
    map_isIntegral_int (IsCMField.complexConj E) hy
  have hfix : ∀ y : FR E, IsCMField.complexConj E (y : E) = y := fun y =>
    IsCMField.complexConj_apply_eq_self E y
  set r := θ - IsCMField.complexConj E θ with hrdef
  have hri : IsIntegral ℤ r := hθ.sub (hc _ hθ)
  have h0 : IsIntegral ℤ ((x 0 : E) * r) := by
    have := hu.sub (hc _ hu)
    rw [map_add, map_mul, hfix, hfix] at this
    have e : (x 0 : E) * r = (x 0 : E) * θ + (x 1 : E) -
        ((x 0 : E) * IsCMField.complexConj E θ + (x 1 : E)) := by rw [hrdef]; ring
    rw [e]; exact this
  have h1 : IsIntegral ℤ ((x 1 : E) * r) := by
    have := (hu.mul hri).sub (h0.mul hθ)
    have e : (x 1 : E) * r = ((x 0 : E) * θ + (x 1 : E)) * r - (x 0 : E) * r * θ := by ring
    rw [e]; exact this
  have hj : IsIntegral ℤ ((x j : E) * r) := by
    fin_cases j
    · exact h0
    · exact h1
  have hD' : (D : E) = -r ^ 2 := by rw [hr]; ring
  have hinj : Function.Injective (algebraMap (FR E) E) := (algebraMap (FR E) E).injective
  have hx : algebraMap (FR E) E (x j) = (x j : E) := rfl
  constructor
  · rw [← isIntegral_algebraMap_iff hinj, map_mul, map_pow, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) ^ 2 = -((x j : E) * r * ((x j : E) * r)) := by ring
    rw [e]; exact (hj.mul hj).neg
  · rw [← isIntegral_algebraMap_iff hinj, map_mul, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) = -((x j : E) * r * r) := by ring
    rw [e]; exact (hj.mul hri).neg

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFiniteEtaleOfExistsUniqueLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isIso_of_finite_etale_of_existsUnique_lift (W S : Scheme.{0}) (w : W ⟶ S) (hf : IsFinite w)
    (he : Etale w) (hc : PreconnectedSpace S) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S)
    (hs : ∃! x : Sp Ω ⟶ W, x ≫ w = s) : IsIso w := by
  obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨x₀, hx₀, hu⟩ := hs
  have hsub : Subsingleton {x : Sp Ω ⟶ W // x ≫ w = s} :=
    ⟨fun a b => Subtype.ext ((hu a.1 a.2).trans (hu b.1 b.2).symm)⟩
  have hne : Nonempty {x : Sp Ω ⟶ W // x ≫ w = s} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨_, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank w s z
  have h1 : w.finrank (s z) = 1 := by
    rw [← hcard, Nat.card_eq_one_iff_unique]
    exact ⟨hsub, hne⟩
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext y
  rw [Pi.one_apply, ← h1]
  exact (Scheme.Hom.isLocallyConstant_finrank w).apply_eq_of_preconnectedSpace y (s z)

end GlobalTheory.Mum
end

