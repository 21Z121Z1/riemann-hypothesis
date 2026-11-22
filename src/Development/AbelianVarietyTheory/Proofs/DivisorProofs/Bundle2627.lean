import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

def TraitRed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    {B L : LB G.left} {N : ℕ} (s : Fin (N + 1) → B.Sec) (θ : L.Sec) (Y : Over (Sp (ResidueField R))) [GrpObj Y]
    (j : Y.left ⟶ PSpace R N) (O : Y.left.Opens) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (s i) (p' ≫ β)) hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → (p' ≫ β) x ∈ nonzeroLocus θ

def embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) : X.Opens := ⨆ i, nonzeroLocus (s i)

theorem iSup_nonzeroLocus_embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) :
    ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (embH s).ι) = ⊤ := by
  simp only [GlobalTheory.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

def embF {R : Type} [CommRing R] {X : Scheme.{0}} {B : LB X} {N : ℕ} (q : X ⟶ Sp R) (s : Fin (N + 1) → B.Sec) :
    (embH s).toScheme ⟶ PSpace R N :=
  GlobalTheory.ProjSpace.toProj ((embH s).ι ≫ q) (fun i => GlobalTheory.secPull (s i) (embH s).ι) (iSup_nonzeroLocus_embH s)

end GlobalTheory.Mum.SecEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
section
noncomputable section

open IsLocalRing GlobalTheory.Toroidal

namespace GlobalTheory.MonoVal

theorem eq_span_monomial_of_forall_cdvr (k : Type) [Field k] [CharZero k] (m e : ℕ) (I : Ideal (ChartRing k m e))
    (a : Fin m → ℕ)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : ChartRing k m e →+* W,
      Function.Injective ψ → IsLocalHom ψ → I.map ψ = Ideal.span {ψ (∏ i, bdParam k m e i ^ a i)}) :
    I = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  set q : ChartRing k m e := ∏ i, bdParam k m e i ^ a i with hqdef
  haveI : CharZero (ChartRing k m e) := (MvPowerSeries.constantCoeff : ChartRing k m e →+* k).charZero
  obtain ⟨hN, hIC, -, -⟩ := GlobalTheory.ChartCone.isCN_chartRing k m e
  haveI := hN
  haveI := hIC
  have hX : ∀ j : Fin m ⊕ Fin e, (MvPowerSeries.X j : ChartRing k m e) ≠ 0 := by
    intro j hj
    have := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hj
    simp [MvPowerSeries.coeff_X] at this
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hX _)
  have loc_of : ∀ {V : Type} [CommRing V] [IsLocalRing V] (φ : ChartRing k m e →+* V),
      (maximalIdeal V).comap φ = maximalIdeal (ChartRing k m e) → IsLocalHom φ := by
    intro V _ _ φ hφ
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hx' : x ∈ maximalIdeal (ChartRing k m e) := hnu
    rw [← hφ, Ideal.mem_comap] at hx'
    exact hx' hx

  have hle : I ≤ Ideal.span {q} := by
    intro f hf
    rw [Ideal.mem_span_singleton]
    refine GlobalTheory.ValCrit.dvd_of_forall_cdvr _ f q hq0 fun V _ _ _ φ hV hinj hφ => ?_
    have hm := h V hV φ hinj (loc_of φ hφ)
    rw [← Ideal.mem_span_singleton, ← hm]
    exact Ideal.mem_map_of_mem φ hf
  refine le_antisymm hle ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  by_contra hqI
  let I' : Ideal (ChartRing k m e) := Submodule.comap (LinearMap.mulLeft (ChartRing k m e) q) I
  have hmemI' : ∀ g, g ∈ I' ↔ q * g ∈ I := fun g => Iff.rfl
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ψ : ChartRing k m e →+* V),
      GlobalTheory.LN.CDvr V → Function.Injective ψ → IsLocalHom ψ → False := by
    intro V _ _ _ ψ hV hinj hψ
    have hmap := h V hV ψ hinj hψ
    have hI : I = Ideal.span {q} * I' := by
      apply le_antisymm
      · intro f hf
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 (hle hf)
        exact Ideal.mem_span_singleton_mul.2 ⟨g, (hmemI' g).2 (by rwa [mul_comm]), mul_comm _ _⟩
      · rw [Ideal.span_singleton_mul_le_iff]
        intro z hz
        exact (hmemI' z).1 hz
    have hψq : ψ q ≠ 0 := (map_ne_zero_iff ψ hinj).2 hq0
    have htop : Ideal.map ψ I' = ⊤ := by
      have h2 : Ideal.span {ψ q} * Ideal.map ψ I' = Ideal.span {ψ q} * ⊤ := by
        have h3 : Ideal.map ψ (Ideal.span {q} * I') = Ideal.span {ψ q} * Ideal.map ψ I' := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
        rw [Ideal.mul_top, ← h3, ← hI, hmap]
      exact (Ideal.span_singleton_mul_right_inj hψq).1 h2
    have hI'ne : I' ≠ ⊤ := by
      intro ht
      apply hqI
      have h1 : (1 : ChartRing k m e) ∈ I' := ht ▸ Submodule.mem_top
      simpa using (hmemI' 1).1 h1
    have hle' : Ideal.map ψ I' ≤ maximalIdeal V := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' := IsLocalRing.le_maximalIdeal hI'ne hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx'
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx' (isUnit_of_map_unit ψ x hu)
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (htop ▸ hle'))
  rcases isEmpty_or_nonempty (Fin m ⊕ Fin e) with hσ | hne
  ·
    let ψ0 : ChartRing k m e →+* PowerSeries k :=
      (PowerSeries.C : k →+* PowerSeries k).comp (MvPowerSeries.constantCoeff : ChartRing k m e →+* k)
    have hc : ∀ f : ChartRing k m e, f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      intro f
      ext n
      have hn : n = 0 := Subsingleton.elim _ _
      subst hn
      simp
    have hinj : Function.Injective ψ0 := by
      intro f g hfg
      have h1 : MvPowerSeries.constantCoeff f = MvPowerSeries.constantCoeff g := by
        simpa [ψ0] using congrArg PowerSeries.constantCoeff hfg
      rw [hc f, hc g, h1]
    have hloc : IsLocalHom ψ0 := by
      refine ⟨fun f hf => ?_⟩
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      have h1 : IsUnit (PowerSeries.constantCoeff (ψ0 f)) := hf.map _
      simpa [ψ0] using h1
    exact key (PowerSeries k) ψ0 (GlobalTheory.FrameGen.cDvr_powerSeries k) hinj hloc
  · obtain ⟨j⟩ := hne
    have hdvd : (MvPowerSeries.X j : ChartRing k m e) ∣ 1 :=
      GlobalTheory.ValCrit.dvd_of_forall_cdvr _ 1 _ (hX j) fun V _ _ _ φ hV hinj hφ =>
        (key V φ hV hinj (loc_of φ hφ)).elim
    have hu := isUnit_of_dvd_one hdvd
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
    simp at hu

end GlobalTheory.MonoVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem sec_linear : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ∀ i : L.B.ι, (s x).f i = ∑ k, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) (β k) * (s (u k)).f i := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev m β u x hx i
  have hw : ∃ w' : W, ev w' ≠ 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨N, n, b, g, A, c, gw, -, -, hb, -⟩ := hM.fs
    exact hev (b.ext fun j => by rw [hb j, map_sum]; simp [map_smul, hne])
  obtain ⟨w', hw'⟩ := hw
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have ha : ψ (ev w') ≠ 0 := (map_ne_zero ψ).mpr hw'
  have hr : ∀ y : W, ψ (ev w') * GlobalTheory.Cartier.fnOf _ hU ((s y).f i) =
      ψ (ev y) * GlobalTheory.Cartier.fnOf _ hU ((s w').f i) := fun y => (hM.ratio y w' i hU).symm
  have hc : ∀ b : 𝓞 K, GlobalTheory.Cartier.fnOf _ hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) b) =
      ψ (algebraMap K Ω (b : K)) := by
    intro b
    rw [hM.base]
    exact RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p _ hU) b
  have hex : ψ (ev x) = ∑ k, ψ (algebraMap K Ω (β k : K)) * ψ (ev (u k)) := by
    rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← IsScalarTower.algebraMap_smul K (β k) (u k : V), map_smul, Algebra.smul_def, map_mul]
  rw [map_sum]
  simp only [map_mul, hc]
  apply mul_left_cancel₀ ha
  rw [hr x, hex, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm (ψ (ev w')), hr (u k), mul_assoc]

end GlobalTheory.ImageModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailFurther
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem LabCover.exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (M' : Modif R) (h : M'.S ⟶ C.S), M'.gp ≫ h = C.gp → h ≫ C.π = M'.π → ∃ (C' : LabCover D) (eS : C'.S ≅ M'.S) (β : C'.G.left ⟶ C.G.left), eS.hom ≫ M'.π = C'.π ∧ IsGrpPullback C'.G C.G (eS.hom ≫ h) β ∧ LBIso C'.P.L.L (C.P.L.L.pull β) := by
  intro R _ _ _ D C M' h hgp hπ
  have hex : ∃ (P' : GlobalTheory.UU.CP ((Over.pullback h).obj C.G)) (w : _),
      GlobalTheory.UU.IsCPMap P' C.P h (pullback.fst C.G.hom h) pullback.condition w :=
    GlobalTheory.UU.exists_pull C.P (GlobalTheory.UU.toBase_mul_pullback C.G h)
  obtain ⟨P', w, hP⟩ := hex
  have hG : IsGrpPullback ((Over.pullback h).obj C.G) C.G h (pullback.fst C.G.hom h) := isGrpPullback_pullback C.G h
  have hw : LBIso P'.L.L (C.P.L.L.pull (pullback.fst C.G.hom h)) := ⟨w, hP.gen⟩

  have key : ∀ {Y : Scheme.{0}} (b : Y ⟶ ((Over.pullback h).obj C.G).left) (c : Y ⟶ C.G.left),
      c = b ≫ pullback.fst C.G.hom h → LBIso (P'.L.L.pull b) (C.P.L.L.pull c) := fun b c e =>
    LBIso.chartPull (chartPullId _) (GlobalTheory.RigidBundleGlue.chartPullComp C.P.L.L _ b c e)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hw b)
  let α' : C.A.A.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift C.α (C.A.A.hom ≫ M'.gp) (by rw [C.α_cart.1.w, Category.assoc, hgp])
  have hα : α' ≫ pullback.fst C.G.hom h = C.α := pullback.lift_fst _ _ _
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj C.G
            semi := IsSemiAbelian.pullback h C.G C.semi
            P := P'
            A := C.A
            α := α'
            α_cart := IsGrpPullback.cancel hG (C.α_cart.congr hgp.symm hα.symm) (pullback.lift_snd _ _ _)
            α_lb := LBIso.trans C.A.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) C.α_lb
              (LBIso.symm (key α' C.α hα.symm))
            n := C.n
            n_prime := C.n_prime
            n_odd := C.n_odd
            n_unit := C.n_unit
            lab := C.lab
            trait := ?_ }, Iso.refl _, pullback.fst C.G.hom h, Category.id_comp _,
      hG.congr (Category.id_comp _).symm rfl, hw⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, _, β, D', A', U', hD, hW', hio, hfin, hcart, hlb, hlab⟩ :=
    C.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  let β' : G''.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift β (G''.hom ≫ spMap io ≫ ξ) (by rw [hcart.1.w, Category.assoc, Category.assoc])
  have hβ : β' ≫ pullback.fst C.G.hom h = β := pullback.lift_fst _ _ _
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, inferInstance, β', D', A', U', hD, hW',
    hio, hfin, IsGrpPullback.cancel hG (hcart.congr (Category.assoc _ _ _).symm hβ.symm) (pullback.lift_snd _ _ _),
    LBIso.trans U'.LG.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) hlb (LBIso.symm (key β' β hβ.symm)), ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hlab F em hF j p p₁ p' x' h₁ h₂ h₃ ?_
  have e := congrArg (· ≫ pullback.fst C.G.hom h) h₄
  simp only [Category.assoc, hβ, hα] at e
  simpa only [Category.assoc] using e

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def lnDet {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (τ : E →+* ℂ) : ℝ :=
  ∑ i, Real.log (Pad.grNorm t x (latHT t p x) (u τ) i) - ∑ j, Real.log (Pad.grNorm t x (latHT t p x) (u (conjEmb τ)) j)

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def InducesPl (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] : Prop :=
  ∀ a : c.F, ‖algebraMap c.F ℂ_[p] a‖ ≤ 1 ↔ la.valuation c.F a ≤ 1

variable {p : ℕ} [Fact p.Prime]

def IsAlgFr [Algebra c.F ℂ_[p]] (P : FrPt Xo c ℂ_[p]) : Prop :=
  ∃ (K : Type) (_ : Field K) (k : K →+* ℂ_[p]) (z : Sp K ⟶ Xo.XF c), (∀ a : K, IsAlgebraic ℤ a) ∧ GlobalTheory.AllWt.ptF P = spMap k ≫ z

def IsTestAt (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [Algebra c.F ℂ_[p]] (P : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X) : Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = GlobalTheory.AllWt.ptF P ≫ Z.j ∧
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ Z.X), T.FinRes ∧ Function.Injective kO ∧ spMap kO ≫ yT = yb

def PtAt [StarRing (𝓞 E)] (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X) (yy : Sp ℂ_[p] ⟶ Xo.XF c)
    (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left) : Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Z.j ∧ IsGrpPullback Q.G Z.t.G yb π ∧
    (∀ a, (Q.oG.act a).left ≫ π = π ≫ (Z.t.act.act a).left) ∧ IsGrpPullback Q.A.A Z.oF.t.G yy ψ ∧
    ψ ≫ Z.m.φ = Q.gen ≫ π

def DetConst (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (Zc : Formalism.L2.Pj.Comp Xo c) (τ : E →+* ℂ) (f : Rul Xo c) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime], ∃ ρ : ℝ, ∀ [Algebra c.F ℂ_[p]], InducesPl la p →
    ∀ P : FrPt Xo c ℂ_[p], IsAlgFr P → GlobalTheory.AllWt.LiesOn Zc P → evR Xo c f P ≠ 0 ∧
      Real.log ‖evR Xo c f P‖ + lnDet Z.t p (GlobalTheory.AllWt.ptF P ≫ Z.j) (frameOf Z P).v τ = ρ

end Defs

def RegLocSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (U W : V.X.Opens), (W : Set V.X).Nonempty →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (g : V.X.functionField),
    (∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      below (z ≫ V.j) ∈ W → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) →
    ∀ x ∈ U, (V.p x).asIdeal = v.asIdeal → RegAt x g

def GeoSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, TrueGeo.Pts Y σ → ℝ) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → TrueGeo.AlgPt Y → ℝ),
    Norms V L f a lg → ∀ (s : Y.Fn) (W : Y.X.Opens), (W : Set Y.X).Nonempty → ∀ l : ℕ, l.Prime →
    (∀ v : HeightOneSpectrum (𝓞 F), (l : 𝓞 F) ∈ v.asIdeal → ∃ ρ : ℝ, ∀ (e : TrueGeo.Ext v) (y : TrueGeo.AlgPt Y),
      below y.1 ∈ W → UnitAt (below y.1) (s / f (below y.1)) ∧
        Real.log (e.w (TrueGeo.valAt y.1 (s / f (below y.1)))) + lg v e y = ρ) → NefOver L l

def AnyLevSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ q : ℕ, q.Prime → l.GoodAt q) →
    (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → GlobalTheory.CompRat.CurveOver H c.F l.M' →
    ∀ (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H), ∃ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0),
      ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ ρ : ℝ, ∀ w ∈ htValOn Zc la, w f = (ρ : EReal)

def TestPtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) [Fact p.Prime]
    [Algebra c.F ℂ_[p]] (P : FrPt Xo c ℂ_[p]), IsAlgFr P → ∃ yb, IsTestAt Z P yb

def ExFrameSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q →
    ∀ (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (Zc : Formalism.L2.Pj.Comp Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]], InducesPl la p →
    ∀ (P : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X), IsTestAt Z P yb → GlobalTheory.AllWt.LiesOn Zc P →
    ∃ y : FrPt Xo c ℂ_[p], (fun f => val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y)) ∈ htValOn Zc la ∧
      GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF P ∧
      letI := H.starRing; ∃ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left) (z : FrPt Xo c ℂ_[p]),
        PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ ∧ IsHTChange Q (ψ ≫ Z.m0.toSABMap.φ) z y

def BridgeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    [IsLocallyNoetherian X] [X.IsSeparated] (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (Q : PtP E p)
    (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : Q.G.left ⟶ t.G.left), IsGrpPullback Q.G t.G yb π →
    ∀ (n : ℕ) (x : Fin n → LieG Q.Gt) (u : Fin n → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)),
    (∀ j, LieTie Q (Q.gen ≫ π) (x j) (u j)) → ∀ (a : Fin n → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
    IsCombAtG t (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) u a w →
      (w ∈ latHT t p (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) ↔ ∑ j, a j • Q.bLie (x j) ∈ Q.latT)

def EigSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ)
    [Fact p.Prime], ∃ δ : ℂ_[p], δ ≠ 0 ∧ ∀ (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]] [StarRing (𝓞 E)] (Q : PtP E p)
      (τ : Psi H) (w : Q.V), w ∈ Q.eigV (embInt c Q.integers τ.1) → (w ∈ htLat c Q τ.1 ↔ δ • w ∈ Q.latT)

def CovolSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left))
    (m : ℕ) (u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (g : Matrix (Fin m) (Fin m) C) (δ : C), δ ≠ 0 →
    (∀ k, IsTanAtG t x (u' k)) → (∀ a a' w, IsCombAtG t x u' a w → IsCombAtG t x u' a' w → a = a') →
    (∀ a w, IsCombAtG t x u' a w → (w ∈ Λ ↔ ∀ i, ‖δ * a i‖ ≤ 1)) → (∀ i, IsCombAtG t x u' (g i) (u i)) → g.det ≠ 0 →
    ∑ i, Real.log (Pad.grNorm t x Λ u i) = Real.log ‖g.det‖ + m * Real.log ‖δ‖

def PointSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (τ : Psi H) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [Algebra c.F ℂ_[p]],
    ∀ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0), ∀ (P y z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF P →
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ → IsHTChange Q (ψ ≫ Z.m0.toSABMap.φ) z y → evR Xo c f y ≠ 0 →
      evR Xo c f P ≠ 0 ∧ Real.log ‖evR Xo c f P‖ + lnDet Z.t p (GlobalTheory.AllWt.ptF P ≫ Z.j) (frameOf Z P).v τ.1 =
        Real.log ‖evR Xo c f y‖ + K

def FlagSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H),
    ∀ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0), (letI := (constF e Y.Y).toAlgebra; GlobalTheory.AllWt.LiesOn Zc Y.y0) →
    DetConst Z Zc τ.1 f → ∀ (N : ℕ), Dw.p + Dw.q = N → ∀ (a : ℕ → Bool) (R : Option ℝ) (v : HeightOneSpectrum (𝓞 F)),
    a (resP v) = true → ∃ ρ : ℝ, ∀ (ε : TrueGeo.Ext v) (y : TrueGeo.AlgPt Y.Y), Y.π (below y.1) ∉ genBd Z →
      UnitAt (below y.1) (Y.val f / ∏ i : Fin N, genAt (divOf Y (expo Dw (rootSym Dw a R τ.1 i))) (below y.1)) ∧
      Real.log (ε.w (TrueGeo.valAt y.1
        (Y.val f / ∏ i : Fin N, genAt (divOf Y (expo Dw (rootSym Dw a R τ.1 i))) (below y.1)))) +
        ∑ i : Fin N, lgOf Y (rootSym Dw a R τ.1 i) v ε y = ρ

end GlobalTheory.DetHT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

theorem fix_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
    ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hI hT L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ω hω s hs g h hg hh
  obtain ⟨unr, odd, intS, intT, hermS, hermT, hδ, psiInt, psiNe, hAt, hSurj, hLat, hPsi, hEq, hιS, hιT, hKS, hKT⟩ := hC
  have hvac : G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := hs ▸ s.2
  have h1 : ω (1, h) s = s := by
    have hA : Acts (evFin F v) (om' (ιS 1, ιT h)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (G.M'.vac v) := by
      rw [map_one, hs]
      exact GlobalTheory.T.inertPlace_latticeStabilizer_fixes_vacuum F E σ B a a' G X om om' hTr v w hI hT (ιT h) (hKT h hh)
    exact Subtype.ext (((hω 1 h s _ hvac).mp hA).trans hs.symm)
  have h2 : ω (g, 1) s = s := by
    have hA : Acts (evFin F v) (om' (ιS g, ιT 1)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (G.M'.vac v) := by
      rw [map_one, hs]
      exact GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hTr v w hI hT (ιS g) (hKS g hg)
    exact Subtype.ext (((hω g 1 s _ hvac).mp hA).trans hs.symm)
  have hgh : ((g, h) : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)) = (g, 1) * (1, h) := by
    simp
  rw [hgh, map_mul, Module.End.mul_apply, h1, h2]

end GlobalTheory.InertBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfDualMapSurjectiveOfProjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem injective_of_dualMap_surjective_of_projective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Projective R M]
      (N : Type) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
      Function.Surjective f.dualMap → Function.Injective f := by
  intro R _ M _ _ _ N _ _ f hf
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  refine (Module.forall_dual_apply_eq_zero_iff R m).mp fun φ => ?_
  obtain ⟨ψ, rfl⟩ := hf φ
  simp [LinearMap.dualMap_apply, hm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameStalkCompatibilityStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_stalk_compatibility : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  first | exact @GlobalTheory.HSApp.germ_eq_unit_mul_evI | exact GlobalTheory.HSApp.germ_eq_unit_mul_evI | (intros; apply GlobalTheory.HSApp.germ_eq_unit_mul_evI <;> assumption)
end

