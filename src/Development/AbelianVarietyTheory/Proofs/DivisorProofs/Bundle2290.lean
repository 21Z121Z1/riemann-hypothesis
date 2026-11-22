import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackDimSuccDivisorsEqZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem Dbl.num_eq_zero_of_isPull : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (q : W.Z ⟶ Y.X) [IsDominant q] (y : Fin (Y.dim + 1) → CartierDiv W.Z) (e : Fin (Y.dim + 1) → Y.Dv), (∀ i, IsPull q (y i) (e i)) → W.num y = 0 := by
  intro F _ Y W hW q _ y e h
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hp : IsProjOver (strHom F W.Z) := by
    rw [strHom_eq (f := W.p₁ ≫ Y.str) fun _ => rfl]
    exact W.proj
  have hd : topologicalKrullDim W.Z ≤ (0 + (Y.dim + 1) : ℕ) := by
    rw [Nat.zero_add]; exact hW
  have hg : topologicalKrullDim (closure ({q (genericPoint W.Z)} : Set Y.X)) < (Y.dim + 1 : ℕ) := by
    refine lt_of_le_of_lt (topologicalKrullDim_subspace_le _ _) ?_
    rw [Y.topologicalKrullDim_eq]
    exact_mod_cast Nat.lt_succ_self _
  have key := GlobalTheory.PullVanish.interNum_pull_eq_zero F 0 (Y.dim + 1) W.Z Y.X hp hd q hg Fin.elim0
    (fun i => i.elim0) (fun i => toLB (e i)) (fun i => isLB_toLB _)
  have hL : ∀ x, (Sum.elim (Fin.elim0 : Fin 0 → LB W.Z) (fun a => (toLB (e a)).pull q) x).IsLB := by
    rintro (i | a)
    · exact i.elim0
    · exact pull_isLB (isLB_toLB _) q
  rw [← interNum_comp_equiv F _ hL (Equiv.emptySum (Fin 0) (Fin (Y.dim + 1))).symm] at key
  refine Eq.trans ?_ key
  refine interNum_congr_cls F _ (fun i => isLB_toLB _) (fun i => hL _) fun i => ?_
  exact ((cls_pull (isLB_toLB (e i)) q (pull_isLB (isLB_toLB _) q)).trans
    (GlobalTheory.Cartier.PullPres.pull_cls_toLB _ _ q (y i) (e i) (h i))).symm

end GlobalTheory.FlagPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.LogPole

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev toBase (TF : TorFlag Xo c) (Z : Comp Xo c) : Y₀ TF.X Z ⟶ TF.Y.X := inc₀ TF.X Z ≫ TF.X.π

def IsEigBasis (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) : Prop :=
  (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX TF.Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)

def IsCell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) : Prop :=
  IsAffineOpen W ∧ W ≤ toBase TF Z ⁻¹ᵁ U.1 ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧
    (∀ σ i j, i < j → L σ i j = 0) ∧ (∀ σ i, IsUnit (L σ i i)) ∧
    (∀ σ i j, j < i → N σ i j = 0) ∧ (∀ σ i, N σ i i = 1) ∧
    ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1)
      (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z)
      (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG TF.Y.t (z ≫ toBase TF Z)
        (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩))
        (fun j => ev z W hz ((L σ * N σ) i j)) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left

def cellCoord {R : Type} (N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R) (a : VIx Dw) : R :=
  N a.1 a.2.1.1 a.2.1.2

def IsBaseFrame (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) {K : Type} [CommRing K] [Algebra c.F K]
    (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) : Prop :=
  ∀ σ i, (tv (frVec TF.Y P rfl σ i)).left = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, i⟩)

def KSCompare (TF : TorFlag Xo c) (s : ℚ) : Prop :=
  ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v →
    ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)
      (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ →
    ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1),
      IsBaseFrame TF U e v P hU →
    ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1),
      y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) →
      (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) +
        TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) →
      FlagTan.IsKS (psiSet H) P (y' ≫ pullback.fst _ _) fun k =>
        (s : K) * ev (frX P ≫ TF.Y.j) U.1 hU (Θ (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩))

def logDet {R : Type} [CommRing R] {m : ℕ} (b : Fin m → Derivation ℤ R R) (x : Fin m → R) : R :=
  (Matrix.of fun i j => b j (x i)).det

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem mem_basicOpen_iff {X : Scheme.{0}} {k : Type} [Field k] (g : Sp k ⟶ X) (s : Γ(X, ⊤)) :
    g (default : PrimeSpectrum k) ∈ X.basicOpen s ↔ IsUnit (g.appTop.hom s) := by
  have p : g ⁻¹ᵁ X.basicOpen s = (Sp k).basicOpen (g.appTop.hom s) := Scheme.preimage_basicOpen g s
  constructor
  · intro H
    refine RingedSpace.isUnit_of_isUnit_germ (Sp k).toRingedSpace ⊤ _ fun y hy => ?_
    have : y ∈ (Sp k).basicOpen (g.appTop.hom s) := by
      rw [← p]
      have e : y = (default : PrimeSpectrum k) := Subsingleton.elim (α := PrimeSpectrum k) _ _
      rw [e]
      exact H
    exact ((Sp k).mem_basicOpen _ y hy).1 this
  · intro H
    have : (default : PrimeSpectrum k) ∈ g ⁻¹ᵁ X.basicOpen s := by
      rw [p, Scheme.basicOpen_of_isUnit _ H]; trivial
    exact this

theorem exists_geometricPoint {X : Scheme.{0}} (x : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (g : Sp k ⟶ X), g (default : PrimeSpectrum k) = x := by
  refine ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
      X.fromSpecResidueField x, ?_⟩
  exact Scheme.fromSpecResidueField_apply x _

theorem avg_cases {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {m w : R} (hm : m * n = 1) (hw : w ^ n = 1) :
    (w = 1 → m * ∑ i ∈ Finset.range n, w ^ i = 1) ∧ (w ≠ 1 → m * ∑ i ∈ Finset.range n, w ^ i = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [h] using hm
  · have h₀ : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by rw [geom_sum_mul, hw, sub_self]
    rw [(mul_eq_zero.1 h₀).resolve_right (sub_ne_zero.2 h), mul_zero]

end GlobalTheory.UnitLocus

namespace GlobalTheory

open UnitLocus in

theorem loc_units_eq :
    ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  intro X N c₀ u hN hc hu
  obtain ⟨m, hm⟩ := hN.exists_left_inv
  let w : Γ(X, ⊤) := (c₀ * u⁻¹).val
  let e : Γ(X, ⊤) := m * ∑ i ∈ Finset.range N, w ^ i
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X),
      (g (default : PrimeSpectrum k) ∈ X.basicOpen e ↔
        Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) ∧
      (g (default : PrimeSpectrum k) ∈ X.basicOpen (1 - e) ↔
        ¬ Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
    intro k _ _ g
    have : IsDomain Γ(Sp k, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain k
    have hval : g.appTop.hom w =
        (Units.map g.appTop.hom.toMonoidHom c₀ * (Units.map g.appTop.hom.toMonoidHom u)⁻¹).val := by
      rw [← map_inv, ← map_mul]; rfl
    have h1 : Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u ↔
        g.appTop.hom w = 1 := by
      rw [hval, Units.val_eq_one, mul_inv_eq_one]
    have hw : g.appTop.hom w ^ N = 1 := by
      rw [hval, ← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hu, ← map_pow, hc, map_one, inv_one,
        _root_.mul_one, Units.val_one]
    have hm' : g.appTop.hom m * N = 1 := by
      have := congrArg g.appTop.hom hm
      rwa [map_mul, map_natCast, map_one] at this
    have he : g.appTop.hom e = g.appTop.hom m * ∑ i ∈ Finset.range N, g.appTop.hom w ^ i := by
      simp only [e, map_mul, map_sum, map_pow]
    obtain ⟨a, b⟩ := avg_cases hm' hw
    rw [mem_basicOpen_iff, mem_basicOpen_iff, h1, map_sub, map_one, he]
    by_cases h : g.appTop.hom w = 1
    · rw [a h]; simp [h]
    · rw [b h]; simp [h]
  refine ⟨X.basicOpen e, ⟨?_, (X.basicOpen e).isOpen⟩, fun k _ _ g => (key k g).1⟩
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    obtain ⟨k, _, _, g, rfl⟩ := exists_geometricPoint x
    exact (key k g).1.trans (not_not.symm.trans (not_congr (key k g).2.symm))
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_section_projective_over_field : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X), IsProjOver q → z ≫ q = 𝟙 _ → IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  first | exact @GlobalTheory.secClosed_closedPoint | exact GlobalTheory.secClosed_closedPoint | (intros; apply GlobalTheory.secClosed_closedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensional
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.RestrictDVR

theorem isDiscreteValuationRing_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (hfin : (letI := φ.toAlgebra; FiniteDimensional K L))
    (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap φ) := by
  letI := φ.toAlgebra
  set E := V.comap φ with hE
  have memE : ∀ x : K, x ∈ E ↔ φ x ∈ V := fun x => ValuationSubring.mem_comap
  let g : E →+* V := (φ.comp E.subtype).codRestrict V (fun x => (memE x).1 x.2)
  have hg : ∀ x : E, ((g x : V) : L) = φ x := fun x => rfl

  have hpid : IsPrincipalIdealRing E := by
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊥
    · subst hI; exact bot_isPrincipal
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f : E → ℕ∞ := fun y => IsDiscreteValuationRing.addVal V (g y)
    let s : Set E := {y | y ∈ I ∧ y ≠ 0}
    have hs : x ∈ s := ⟨hxI, hx0⟩
    set x0 := Function.argminOn f s ⟨x, hs⟩ with hx0def
    have hx0s : x0 ∈ s := Function.argminOn_mem f s ⟨x, hs⟩
    refine ⟨x0, le_antisymm ?_ ?_⟩
    · intro y hy
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      by_cases hy0 : y = 0
      · exact ⟨0, by simp [hy0]⟩
      have hle : f x0 ≤ f y := Function.argminOn_le f s ⟨hy, hy0⟩
      obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).1 hle
      have hx0K : (x0 : K) ≠ 0 := fun h => hx0s.2 (Subtype.ext h)
      have hφx0 : φ x0 ≠ 0 := (map_ne_zero φ).2 hx0K
      have hcL : φ ((y : K) / x0) = (c : L) := by
        have := congrArg Subtype.val hc
        simp only [hg, MulMemClass.coe_mul] at this
        rw [map_div₀, this]; field_simp
      refine ⟨⟨(y : K) / x0, (memE _).2 (hcL ▸ c.2)⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul]
      field_simp
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
      exact hx0s.1

  have hnf : IsLocalRing.maximalIdeal E ≠ ⊥ := by
    intro hbot
    have hall : ∀ x : K, φ x ∈ V := by
      intro x
      rcases E.mem_or_inv_mem x with h | h
      · exact (memE x).1 h
      by_cases hx : x = 0
      · simp [hx]
      have hu : IsUnit (⟨x⁻¹, h⟩ : E) := by
        by_contra hnu
        have : (⟨x⁻¹, h⟩ : E) ∈ IsLocalRing.maximalIdeal E := hnu
        rw [hbot, Ideal.mem_bot] at this
        exact inv_ne_zero hx (congrArg Subtype.val this)
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have : x = (u : K) := by
        have h1 := congrArg Subtype.val hu
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
        field_simp at h1; exact h1.symm
      rw [this]; exact (memE _).1 u.2
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    have hπ0 : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    let ψ : K →+* V := φ.codRestrict V hall
    have hint : IsIntegral K ((π : L)⁻¹) := Algebra.IsIntegral.isIntegral _
    obtain ⟨p, hpm, hp⟩ := hint
    have hintV : IsIntegral V ((π : L)⁻¹) := by
      refine ⟨p.map ψ, hpm.map ψ, ?_⟩
      have hcomp : (algebraMap V L).comp ψ = algebraMap K L := by ext; rfl
      rw [Polynomial.eval₂_map, hcomp]
      exact hp
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp hintV
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one y (Subtype.ext ?_)
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    have : (y : L) = (π : L)⁻¹ := hy
    rw [this, mul_inv_cancel₀ hπ0]
  exact { hpid with not_a_field' := hnf }

theorem main : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  intro K L _ _ φ hfin V _
  exact isDiscreteValuationRing_comap K L φ hfin V

end GlobalTheory.RestrictDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigenvectorIntegralOfTangentPullbackMemStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEigenvector_integral_of_tangentPullback_mem : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (w : epsOver T.V T.V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → IsEigV c io G τ w := by
  first | exact @GlobalTheory.TanEigInt.isEigV_of_tanPull_mem | exact GlobalTheory.TanEigInt.isEigV_of_tanPull_mem | (intros; apply GlobalTheory.TanEigInt.isEigV_of_tanPull_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGeneratorTopFormsOfFormallyUnramified
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.TopForm

theorem isFreeGen_formMap_of_formallyUnramified :
    ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  intro k A B _ _ _ α β ψ h n hU ω hω hex
  obtain ⟨ω', hω'⟩ := hex
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ψ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyUnramified A B := hU
  have hspan : Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (ψ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k A B x).mp (Subsingleton.elim _ _)
    induction y with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B a]
        exact Submodule.smul_mem _ _ hx
  have hgen : Submodule.span B {formMap n ψ h ω} = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span B n (Omega β) hspan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun i => hw (Set.mem_range_self i)
    have e : exteriorPower.ιMulti B n w = formMap n ψ h (dForm α v) := by
      rw [formMap_dForm, dForm_eq]
      congr 1
      funext i
      exact (hv i).symm
    rw [SetLike.mem_coe, e, ← hω.repr_smul (dForm α v), map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hmem : ω' ∈ Submodule.span B {formMap n ψ h ω} := hgen ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hb := hω'.repr_smul (formMap n ψ h ω)
  rw [← hb] at hc ⊢
  refine hω'.smul_iff.mpr (IsUnit.of_mul_eq_one c ?_)
  refine hω'.1 ?_
  simp only [mul_comm _ c, mul_smul, one_smul]
  exact hc

end GlobalTheory.TopForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralInConeDegreeOfValuativeBoundStatement
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralInConeDegree_of_valuativeBound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω), CharZero K → FiniteDimensional K V → (⊤ : IntermediateField K Ω).FG → ∀ (τ : ℕ) (t : Ω), ValBound ev τ t → IsIntDeg ev τ t := by
  first | exact @GlobalTheory.DegVal.ValInt.isIntDeg_of_valBound | exact GlobalTheory.DegVal.ValInt.isIntDeg_of_valBound | (intros; apply GlobalTheory.DegVal.ValInt.isIntDeg_of_valBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonemptyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  first | exact @GlobalTheory.isIntegral_of_nonempty_modif | exact GlobalTheory.isIntegral_of_nonempty_modif | (intros; apply GlobalTheory.isIntegral_of_nonempty_modif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisOfCompatibleTangentRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieTransfer

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

theorem rel_comb (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop) (h1 : Rel 1 1)
    (hmul : ∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x'))
    (hsc : ∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x')
    {n : ℕ} (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)) (hr : ∀ j, Rel (y j) (x j))
    (c : Fin n → R) : Rel (comb y c) (comb x c) := by
  classical
  unfold comb
  suffices h : ∀ s : Finset (Fin n), Rel (∏ i ∈ s, epsScale (c i) ≫ y i) (∏ i ∈ s, epsScale (c i) ≫ x i) from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using h1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact hmul _ _ _ _ (hsc (c a) (y a) (x a) _ _ rfl rfl (hr a)) ih

end GlobalTheory.LieTransfer

open GlobalTheory.Reg.VecEig GlobalTheory.LieTransfer in

theorem GlobalTheory.LieTransfer.isLieBasis_of_rel : ∀ (R : Type) [CommRing R] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop), Rel 1 1 → (∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x')) → (∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H), y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x') → (∀ y, IsTangent y → ∃ x, IsTangent x ∧ Rel y x) → (∀ y y' x, IsTangent y → IsTangent y' → Rel y x → Rel y' x → y = y') → (∀ y x x', Rel y x → Rel y x' → x = x') → ∀ (n : ℕ) (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)), IsLieBasis x → (∀ j, IsTangent (y j) ∧ Rel (y j) (x j)) → IsLieBasis y := by
  intro R _ G H _ _ _ _ Rel h1 hmul hsc hex hinj hfun n x y hx hy
  have hyt : ∀ j, IsTangent (y j) := fun j => (hy j).1
  have hrc := rel_comb Rel h1 hmul hsc x y (fun j => (hy j).2)
  refine ⟨hyt, fun w hw => ?_⟩
  obtain ⟨xw, hxw, hrw⟩ := hex w hw
  obtain ⟨c, hc, -⟩ := hx.2 xw hxw
  rw [isLieComb_iff_comb] at hc
  subst hc
  refine ⟨c, (isLieComb_iff_comb _ _ _).2 (hinj w _ _ hw (isTangent_comb hyt c) hrw (hrc c)), ?_⟩
  intro c' hc'
  rw [isLieComb_iff_comb] at hc'
  subst hc'
  have e2 : comb x c = comb x c' := hfun _ _ _ (hrc c') hrw |>.symm
  exact (comb_injective hx e2).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnipotentModIdealLiftLaInvStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnipotentModIdeal_liftLa_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  first | exact @GlobalTheory.OrbitSep.unipAt_inv_liftLa | exact GlobalTheory.OrbitSep.unipAt_inv_liftLa | (intros; apply GlobalTheory.OrbitSep.unipAt_inv_liftLa <;> assumption)
end

