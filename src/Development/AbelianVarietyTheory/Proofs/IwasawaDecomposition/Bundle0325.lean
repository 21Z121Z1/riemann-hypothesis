import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.ClosedPt

variable {ι : Type} {m : ι → ℕ}

theorem par_zero_top {K : Type} [Field K] {g : Mat m K} (h : ∀ τ, (g τ).det ≠ 0) : Par 0 ⊤ g := fun τ =>
  ⟨fun _ _ => trivial, h τ, trivial, fun _ _ hi _ => absurd hi (Nat.not_lt_zero _)⟩

theorem map_mul_inv {R K : Type} [CommRing R] [Field K] (g : R →+* K) (N₁ N₂ : Mat m R) (τ : ι)
    (hu : IsUnit (N₂ τ).det) : (N₁.map g * (N₂.map g)⁻¹) τ = (N₁ τ * (N₂ τ)⁻¹).map g := by
  have e : (N₂ τ).map g * ((N₂ τ)⁻¹).map g = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ g.map_zero g.map_one]
  show (N₁ τ).map g * ((N₂ τ).map g)⁻¹ = _
  rw [Matrix.map_mul, Matrix.inv_eq_right_inv e]

theorem descend {R L : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field L] [Algebra R L]
    [IsFractionRing R L] (N₁ N₂ : Mat m R)
    (h₁ : ∀ τ, (N₁.map (IsLocalRing.residue R) τ).det ≠ 0)
    (h₂ : ∀ τ, (N₂.map (IsLocalRing.residue R) τ).det ≠ 0)
    (hL : Par m ⊤ (N₁.map (algebraMap R L) * (N₂.map (algebraMap R L))⁻¹)) :
    Par m ⊤ (N₁.map (IsLocalRing.residue R) * (N₂.map (IsLocalRing.residue R))⁻¹) := by
  have hu : ∀ τ, IsUnit (N₂ τ).det := fun τ => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    exact h₂ τ
  have hP := (par_zero_top h₁).mul (par_zero_top h₂).inv
  intro τ
  refine ⟨fun _ _ => trivial, hP.det_ne τ, trivial, fun i j hi hij => ?_⟩
  have h0 := (hL τ).2.2.2 i j hi hij
  rw [map_mul_inv _ _ _ τ (hu τ)] at h0
  rw [map_mul_inv _ _ _ τ (hu τ)]
  have h0' : algebraMap R L ((N₁ τ * (N₂ τ)⁻¹) i j) = 0 := h0
  show IsLocalRing.residue R ((N₁ τ * (N₂ τ)⁻¹) i j) = 0
  rw [(map_eq_zero_iff _ (IsFractionRing.injective R L)).1 h0', map_zero]

variable {F : Type} [Field F]

noncomputable def vals {Y : Var F} {R : Type} [CommRing R] [IsLocalRing R] (v : Sp R ⟶ Y.X) (M : Mat m Y.Fn)
    (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) : Mat m R :=
  fun τ a b => RatModel.valLoc (M := ratOf Y) v _ specializes_rfl ⟨M τ a b, hM τ a b⟩

theorem map_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    (M : Mat m Y.Fn) (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) :
    M.map ((ratOf Y).val (spMap σ ≫ v)) = (vals v M hM).map σ := by
  funext τ
  ext a b
  have := RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl ⟨M τ a b, hM τ a b⟩
  exact this

theorem par_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    {M : Mat m Y.Fn} (hM : Par 0 ((ratOf Y).O (v (IsLocalRing.closedPoint R))).toSubring M) :
    Par 0 ⊤ (M.map ((ratOf Y).val (spMap σ ≫ v))) :=
  Par.map_of hM _ (σ.comp (RatModel.valLoc (M := ratOf Y) v _ specializes_rfl))
    (fun x => RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl x)

end GlobalTheory.FlagBundle.ClosedPt

namespace GlobalTheory.FlagBundle.ClosedPt

theorem closedPt_comp {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (v : Sp R ⟶ Z) :
    (spMap (IsLocalRing.residue R) ≫ v) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      v (IsLocalRing.closedPoint R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact congrArg v (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))

theorem gen_specializes {R L : Type} [CommRing R] [IsLocalRing R] [Field L] [Algebra R L] {Z : Scheme.{0}}
    (v : Sp R ⟶ Z) (w : Sp L) : (spMap (algebraMap R L) ≫ v) w ⤳ v (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint (spMap (algebraMap R L) w)).map v.continuous
  convert h using 1
  exact Scheme.Hom.comp_apply _ _ _

end GlobalTheory.FlagBundle.ClosedPt

open GlobalTheory.FlagBundle.ClosedPt in

theorem GlobalTheory.FlagBundle.coBear_closedPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ R _ _ _ L _ _ _ v₁ v₂ e hgen
  have sub₁ := hR₁.2.1
  have sub₂ := hR₂.2.1
  have hf₁ : f₁ (v₁ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) :=
    (Scheme.Hom.comp_apply _ _ _).symm
  have hf₂ : f₂ (v₂ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) := by
    rw [e]; exact (Scheme.Hom.comp_apply _ _ _).symm
  obtain ⟨A, hA⟩ := Eb.nonempty ((v₁ ≫ f₁) (IsLocalRing.closedPoint R))
  obtain ⟨A₁, hA₁⟩ := S₁.nonempty (v₁ (IsLocalRing.closedPoint R))
  obtain ⟨A₂, hA₂⟩ := S₂.nonempty (v₂ (IsLocalRing.closedPoint R))
  have hM₁ := sub₁ _ A₁ hA₁ A (by rw [hf₁]; exact hA)
  have hM₂ := sub₂ _ A₂ hA₂ A (by rw [hf₂]; exact hA)

  obtain ⟨B, hB, hg, hgP, hb1, hb2⟩ := hgen
  have hA₁g : A₁ ∈ S₁.S ((spMap (algebraMap R L) ≫ v₁) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₁ (gen_specializes v₁ _)
  have hA₂g : A₂ ∈ S₂.S ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hAg : A ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact Fr.mem_of_specializes hA (gen_specializes (v₁ ≫ f₁) _)
  have hBg : B ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact hB
  have heq : (spMap (algebraMap R L) ≫ v₁) ≫ f₁ = (spMap (algebraMap R L) ≫ v₂) ≫ f₂ := by
    rw [Category.assoc, Category.assoc, e]
  have hH := par_val (algebraMap R L) v₁ hM₁
  have hself : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (algebraMap R L) ≫ v₁)))
      (spMap (algebraMap R L) ≫ v₁) :=
    ⟨A₁, hA₁g, by rw [Mat.mul_inv hH.det_ne]; exact Par.one⟩
  obtain ⟨A₂', hA₂', hpar⟩ := GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ L _ _ heq A hAg B hBg
    _ hg hself hb1 hb2

  have hsp₂ := gen_specializes (L := L) v₂ (IsLocalRing.closedPoint L)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring
      (A₂ * (A.map φ₂)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y₂) (spMap (algebraMap R L) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint L))
  have hv : ∀ x : ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring,
      (ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ₂)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ₂)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) *
        (A₂ * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one] at hL
  rw [map_val (algebraMap R L) v₁ _ (fun τ a b => (hM₁ τ).1 a b),
    map_val (algebraMap R L) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL

  have hk₁ := par_val (IsLocalRing.residue R) v₁ hM₁
  have hk₂ := par_val (IsLocalRing.residue R) v₂ hM₂
  have hD := descend _ _ (by rw [← map_val]; exact hk₁.det_ne) (by rw [← map_val]; exact hk₂.det_ne) hL
  rw [← map_val, ← map_val] at hD
  have hAk : A ∈ Eb.S ((spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    (congrArg (fun z => A ∈ Eb.S z) (closedPt_comp (v₁ ≫ f₁))).mpr hA
  have hb₁ : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₁) :=
    ⟨A₁, (congrArg (fun z => A₁ ∈ S₁.S z) (closedPt_comp v₁)).mpr hA₁, by
      rw [Mat.mul_inv hk₁.det_ne]; exact Par.one⟩
  have hb₂ : Bears S₂ φ₂ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ S₂.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  exact ⟨A, hAk, _, hk₁, hb₁, hb₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherRowsUpdatedScalars
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem prim_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : PrimRows3 R F)
    (h1 : ∀ i t p v, 0 < lam i t p v) (h2 : (R.updS R.kap lam).PThmB) (h3 : (R.updS R.kap lam).PThmA)
    (h4 : ((R.updS R.kap lam).toCx3 F).GalD F.cr false) : PrimRows3 (R.updS R.kap lam) F := by
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := ⟨h.posScal.1, h1⟩
    levE := h.levE
    h2P := h.h2P
    thmB := h2
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h3
    sumW := h.sumW
    scalConj := h4
    dimParts := h.dimParts }

set_option maxHeartbeats 4000000 in

theorem pins_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (hP : Pins R F cG)
    (hs : (R.updS R.kap lam).IsScal (reFace F Dc Sp Zsc)) : Pins ((R.updS R.kap lam).withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := hP.char
  have hC : (R.updS R.kap lam).WeakCharacterisation (reFace F Dc Sp Zsc) :=
    ⟨h.base, ⟨h.inert.tie, h.inert.onto, h.inert.hR, h.inert.hL, h.inert.SF⟩, h.fullY, h.fullX, h.fullP, hs,
      ⟨h.tup.mu_off, h.tup.mu_used, h.tup.mu_ne, h.tup.mu_conj, h.tup.mu_on⟩, h.phase, h.allPl⟩
  exact ⟨RealDat3.weak_characterisation_with_error hC e, reFace_keep (R.updS R.kap lam) F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩

set_option maxHeartbeats 4000000 in

theorem furtherRows_updatedScalars (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.updS R.kap lam) F := ⟨h.ex, h.conj, h.levelW, h.integral⟩

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.GelfScalar

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def LinAdjOn (D : Submodule ℂ H) (f : H → H) : Prop :=
  (∀ w ∈ D, f w ∈ D) ∧ (∀ v ∈ D, ∀ w ∈ D, f (v + w) = f v + f w) ∧ (∀ (c : ℂ), ∀ w ∈ D, f (c • w) = c • f w) ∧
    ∀ u ∈ D, ∃ u' ∈ D, ∀ w ∈ D, ⟪u, f w⟫_ℂ = ⟪u', w⟫_ℂ

variable {D : Submodule ℂ H}

theorem linAdjOn_id : LinAdjOn D fun w => w := ⟨fun _ hw => hw, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun u hu => ⟨u, hu, fun _ _ => rfl⟩⟩

theorem linAdjOn_zero : LinAdjOn D fun _ => 0 := by
  refine ⟨fun _ _ => D.zero_mem, fun _ _ _ _ => (add_zero 0).symm, fun c _ _ => (smul_zero c).symm,
    fun _ _ => ⟨0, D.zero_mem, fun w _ => ?_⟩⟩
  simp

theorem LinAdjOn.comp {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f (g w) := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => hf1 _ (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show f (g (v + w)) = f (g v) + f (g w)
    rw [hg2 v hv w hw, hf2 _ (hg1 v hv) _ (hg1 w hw)]
  · show f (g (c • w)) = c • f (g w)
    rw [hg3 c w hw, hf3 c _ (hg1 w hw)]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u₁ hu₁
    exact ⟨u₂, hu₂, fun w hw => (h₁ _ (hg1 w hw)).trans (h₂ w hw)⟩

theorem LinAdjOn.add {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f w + g w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => D.add_mem (hf1 w hw) (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_,
    fun u hu => ?_⟩
  · show f (v + w) + g (v + w) = (f v + g v) + (f w + g w)
    rw [hf2 v hv w hw, hg2 v hv w hw]
    abel
  · show f (c • w) + g (c • w) = c • (f w + g w)
    rw [hf3 c w hw, hg3 c w hw, smul_add]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u hu
    refine ⟨u₁ + u₂, D.add_mem hu₁ hu₂, fun w hw => ?_⟩
    show ⟪u, f w + g w⟫_ℂ = ⟪u₁ + u₂, w⟫_ℂ
    rw [inner_add_right, inner_add_left, h₁ w hw, h₂ w hw]

theorem LinAdjOn.smul {f : H → H} (hf : LinAdjOn D f) (a : ℂ) : LinAdjOn D fun w => a • f w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  refine ⟨fun w hw => D.smul_mem a (hf1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show a • f (v + w) = a • f v + a • f w
    rw [hf2 v hv w hw, smul_add]
  · show a • f (c • w) = c • a • f w
    rw [hf3 c w hw, smul_comm]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    refine ⟨(starRingEnd ℂ a) • u₁, D.smul_mem _ hu₁, fun w hw => ?_⟩
    show ⟪u, a • f w⟫_ℂ = ⟪(starRingEnd ℂ a) • u₁, w⟫_ℂ
    rw [inner_smul_right, inner_smul_left, h₁ w hw, Complex.conj_conj]

theorem linAdjOn_sum {ι : Type} (s : Finset ι) {f : ι → H → H} (hf : ∀ i, LinAdjOn D (f i)) :
    LinAdjOn D fun w => ∑ i ∈ s, f i w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact linAdjOn_zero
  · intro i s hi ih
    simp only [Finset.sum_insert hi]
    exact (hf i).add ih

theorem linAdjOn_foldr (l : List (H → H)) (hl : ∀ f ∈ l, LinAdjOn D f) :
    LinAdjOn D fun w => l.foldr (fun f acc => f acc) w := by
  induction l with
  | nil =>
    simp only [List.foldr_nil]
    exact linAdjOn_id
  | cons f l ih =>
    simp only [List.foldr_cons]
    exact (hl f (by simp)).comp (ih fun g hg => hl g (by simp [hg]))

theorem LinAdjOn.exists_extend {f : H → H} (hf : LinAdjOn D f) : ∃ A : H →ₗ[ℂ] H, ∀ w ∈ D, A w = f w := by
  obtain ⟨-, hf2, hf3, -⟩ := hf
  let g : D →ₗ[ℂ] H :=
    { toFun := fun x => f x
      map_add' := fun x y => hf2 x x.2 y y.2
      map_smul' := fun c x => hf3 c x x.2 }
  obtain ⟨A, hA⟩ := LinearMap.exists_extend g
  refine ⟨A, fun w hw => ?_⟩
  have key := LinearMap.congr_fun hA ⟨w, hw⟩
  exact key

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem linAdjOn_dRep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieG G) : LinAdjOn (smSub G π) (dRep π X) := by
  refine ⟨fun w hw => dRep_mem hG hπ hw hX, fun v hv w hw => dRep_add hv hw hX,
    fun c w hw => dRep_smul c hw hX, fun u hu => ⟨-dRep π X u, neg_mem (dRep_mem hG hπ hu hX), fun w hw => ?_⟩⟩
  rw [inner_dRep hG hπ hu hw hX, inner_neg_left]

theorem linAdjOn_dRepC (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (Z : Matrix (Fin n) (Fin n) ℂ) : LinAdjOn (smSub G π) (dRepC G π Z) := by
  obtain ⟨h₁, h₂⟩ := parts_mem hG hh Z
  exact (linAdjOn_dRep hG hπ h₁).add ((linAdjOn_dRep hG hπ h₂).smul Complex.I)

theorem linAdjOn_gelfH (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) :
    LinAdjOn (smSub G π) (gelfH G π k) := by
  show LinAdjOn (smSub G π) fun w => ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC G π (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
      (fun f acc => f acc) w
  refine linAdjOn_sum Finset.univ fun idx => linAdjOn_foldr _ fun g hg => ?_
  rw [List.mem_ofFn] at hg
  obtain ⟨a, rfl⟩ := hg
  exact linAdjOn_dRepC hG hh hπ _

end

theorem gelfH_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (k : ℕ), ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k w = c • w := by
  intro n ε H _ _ _ σ P G hP hPG hσ hirr k
  have hGu : IsUnit G := gram_unit hP hPG
  have hh : Gᴴ = G := gram_herm hPG
  have hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isURepOn_trRep hP hPG hσ
  have hirr' : IsIrredOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isIrredOn_trRep hP hPG hirr
  have hL := linAdjOn_gelfH hGu hh hπ k
  obtain ⟨A, hA⟩ := hL.exists_extend
  obtain ⟨-, -, -, hadj⟩ := hL
  have hnorm : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ v : H, ‖trRep σ P g v‖ = ‖v‖ := fun g hg v => hπ.2.1 g hg v
  have hAg : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      A (trRep σ P g w) = trRep σ P g (A w) := by
    intro g hg w hw
    rw [hA _ (rep_mem hGu hπ hw hg), hA w hw]
    exact GlobalTheory.T.gelfandInvariantAction_commute_unitaryRep_smooth n ε H σ P G hP hPG hσ k g hg w hw
  have h₁ : ∀ (i : Formalism.QuantumDeterminants.UH G) (v : H), ‖trRep σ P i.1 v‖ = ‖v‖ := fun i v => hnorm i.1 i.2 v
  have h₂ : ∀ i : Formalism.QuantumDeterminants.UH G, ∃ j : Formalism.QuantumDeterminants.UH G,
      (∀ v, trRep σ P j.1 (trRep σ P i.1 v) = v) ∧ ∀ v, trRep σ P i.1 (trRep σ P j.1 v) = v := by
    intro i
    have hu : IsUnit i.1.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_mem_UH hGu i.2)
    refine ⟨⟨i.1⁻¹, inv_mem_UH hGu i.2⟩, fun v => ?_, fun v => ?_⟩
    · rw [← rep_mul hπ (inv_mem_UH hGu i.2) i.2, Matrix.nonsing_inv_mul _ hu, rep_one hπ]
    · rw [← rep_mul hπ i.2 (inv_mem_UH hGu i.2), Matrix.mul_nonsing_inv _ hu, rep_one hπ]
  have h₃ : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ S, trRep σ P i.1 v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hinv => hirr' S hS fun g hg v hv => hinv ⟨g, hg⟩ v hv
  have h₄ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ smSub G (trRep σ P), trRep σ P i.1 v ∈ smSub G (trRep σ P) :=
    fun i v hv => rep_mem hGu hπ hv i.2
  have h₅ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P), ‖A (trRep σ P i.1 w)‖ = ‖A w‖ := by
    intro i w hw
    rw [hAg i.1 i.2 w hw, hnorm i.1 i.2]
  have h₆ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ‖(LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)‖ = ‖(LinearMap.id : H →ₗ[ℂ] H) w‖ := by
    intro i w _
    simp only [LinearMap.id_apply]
    exact hnorm i.1 i.2 w
  have h₇ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ⟪A (trRep σ P i.1 w), (LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)⟫_ℂ =
        ⟪A w, (LinearMap.id : H →ₗ[ℂ] H) w⟫_ℂ := by
    intro i w hw
    simp only [LinearMap.id_apply]
    rw [hAg i.1 i.2 w hw, rep_inner hπ i.2]
  have h₈ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f hu hu0 hAu
    apply eq_zero_of_inner_smooth hP hPG hσ
    intro v hv
    obtain ⟨v', -, hvv⟩ := hadj v hv
    have t₁ : Tendsto (fun i => ⟪v, A (u i)⟫_ℂ) atTop (𝓝 ⟪v, f⟫_ℂ) := tendsto_const_nhds.inner hAu
    have t₂ : Tendsto (fun i => ⟪v', u i⟫_ℂ) atTop (𝓝 ⟪v', (0 : H)⟫_ℂ) :=
      tendsto_const_nhds.inner hu0
    rw [inner_zero_right] at t₂
    refine tendsto_nhds_unique t₁ (t₂.congr fun i => ?_)
    rw [hA _ (hu i), hvv _ (hu i)]
  have h₉ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => (LinearMap.id : H →ₗ[ℂ] H) (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f _ hu0 hu
    simp only [LinearMap.id_apply] at hu
    exact tendsto_nhds_unique hu hu0
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant (Formalism.QuantumDeterminants.UH G) H H (fun i => trRep σ P i.1) (smSub G (trRep σ P))
    h₁ h₂ h₃ h₄ A LinearMap.id h₅ h₆ h₇ h₈ h₉
  refine ⟨starRingEnd ℂ c, fun w hw => ?_⟩
  rw [← hA w hw]
  apply ext_inner_smooth hP hPG hσ
  intro u hu
  have e₁ : ⟪A w, u⟫_ℂ = ⟪starRingEnd ℂ c • w, u⟫_ℂ := by
    have e := hc w hw u hu
    rw [LinearMap.id_apply] at e
    rw [e, inner_smul_left, Complex.conj_conj]
  rw [← inner_conj_symm, e₁, inner_conj_symm]

end GlobalTheory.SmVec.GelfScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generically_smooth_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y), GenSmooth M.p Y.dim := by
  first | exact @GlobalTheory.ModelCharts.genSmooth_model | exact GlobalTheory.ModelCharts.genSmooth_model | (intros; apply GlobalTheory.ModelCharts.genSmooth_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOneStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one : ∀ (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ), corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  first | exact @GlobalTheory.LocLanglands.corner_diagT | exact GlobalTheory.LocLanglands.corner_diagT | (intros; apply GlobalTheory.LocLanglands.corner_diagT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonalStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  first | exact @GlobalTheory.CornerUnip.corner_unipB_superDiag | exact GlobalTheory.CornerUnip.corner_unipB_superDiag | (intros; apply GlobalTheory.CornerUnip.corner_unipB_superDiag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOnStatement
section
open MeasureTheory GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedChartDensityMeasure_add_of_compatible_on : ∀ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] {n : ℕ} {κ : Type} (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ (ρ ρ' : κ → Y → ℝ≥0∞), (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ' i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ' j y) → (∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))) → glueMeas e (fun i y => ρ i y + ρ' i y) S = glueMeas e ρ S + glueMeas e ρ' S := by
  first | exact @GlobalTheory.ChartGlue.glueMeas_add_of_compat_on | exact GlobalTheory.ChartGlue.glueMeas_add_of_compat_on | (intros; apply GlobalTheory.ChartGlue.glueMeas_add_of_compat_on <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightLocallyBounded
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftHeight

theorem height_locally_bounded : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ g₀ : GA D V,
    ∃ C : ℝ, ∀ᶠ g in 𝓝 g₀, (height θ V g : ℝ) ≤ C := by
  intro D θ hθ V g₀
  obtain ⟨C, hC, h⟩ := GlobalTheory.Grow.height_comparison V hθ
  have hc := (GlobalTheory.Grow.continuous_height V).continuousAt (x := g₀)
  refine ⟨C * (GlobalTheory.Grow.height V g₀ + 1), ?_⟩
  filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one _)] with g hg
  exact (h g).1.trans (mul_le_mul_of_nonneg_left hg.le hC.le)

end GlobalTheory.Mem.LiftHeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSideStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSeenPrimeCondition_hermitianSide : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, SeenCl (F u).atT := by
  first | exact @GlobalTheory.Mem.Col2.HAt.seenCl_atT | exact GlobalTheory.Mem.Col2.HAt.seenCl_atT | (intros; apply GlobalTheory.Mem.Col2.HAt.seenCl_atT <;> assumption)
end

