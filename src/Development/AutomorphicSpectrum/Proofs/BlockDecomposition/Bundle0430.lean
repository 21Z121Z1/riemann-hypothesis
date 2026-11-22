import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.AutomorphicForms.GLnLocal
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfSmIndFixed
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped Topology

namespace GlobalTheory.CompanionTheory.LeviAdm

theorem finiteDimensional_of_smInd_fixed {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H K : Subgroup G)
    (hK : IsOpen (K : Set G)) (σ : Representation ℂ H W) (A : Submodule ℂ W)
    (hA : ∀ c : H, (c : G) ∈ K → ∀ w ∈ A, σ c w = w)
    (hfd : FiniteDimensional ℂ (fixed (smInd H σ) K)) : FiniteDimensional ℂ A := by
  classical
  have key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → ∀ w ∈ A, σ q w = σ p w := by
    intro p q hpq w hw
    have h1 : σ (p⁻¹ * q) w = w := hA _ (by simpa using hpq) w hw
    have h2 : q = p * (p⁻¹ * q) := by group
    calc σ q w = σ (p * (p⁻¹ * q)) w := by rw [← h2]
      _ = σ p (σ (p⁻¹ * q) w) := by rw [map_mul]; rfl
      _ = σ p w := by rw [h1]
  let S : G → Prop := fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K
  let pick : G → H := fun x => if h : S x then h.choose else 1
  have pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K := by
    intro x h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  let F : A →ₗ[ℂ] (G → W) := LinearMap.pi fun x =>
    if S x then (σ (pick x)).comp A.subtype else 0
  have F_pos : ∀ (w : A) x, S x → F w x = σ (pick x) w := by
    intro w x h
    simp [F, h]
  have F_neg : ∀ (w : A) x, ¬ S x → F w x = 0 := by
    intro w x h
    simp [F, h]
  have S_left : ∀ (q : H) x, S x → S (q * x) := by
    rintro q x ⟨p, hp⟩
    exact ⟨q * p, by simpa [mul_assoc] using hp⟩
  have S_right : ∀ c ∈ K, ∀ x, S x → S (x * c) := by
    rintro c hc x ⟨p, hp⟩
    exact ⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩
  have hlaw : ∀ w : A, F w ∈ indSpace H σ := by
    intro w q x
    by_cases hx : S x
    · have hqx := S_left q x hx
      rw [F_pos w _ hqx, F_pos w _ hx, ← Module.End.mul_apply, ← map_mul]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))
      convert h3 using 1
      simp only [Subgroup.coe_mul]
      group
    · have hqx : ¬ S (q * x) := fun h => hx (by
        have := S_left q⁻¹ _ h
        simpa using this)
      rw [F_neg w _ hqx, F_neg w _ hx, map_zero]
  have hfix : ∀ (w : A), ∀ c ∈ K, ∀ x, F w (x * c) = F w x := by
    intro w c hc x
    by_cases hx : S x
    · have hxc := S_right c hc x hx
      rw [F_pos w _ hxc, F_pos w _ hx]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))
      convert h3 using 1
      group
    · have hxc : ¬ S (x * c) := fun h => hx (by
        have := S_right c⁻¹ (K.inv_mem hc) _ h
        simpa using this)
      rw [F_neg w _ hxc, F_neg w _ hx]
  have hfix' : ∀ (w : A), ∀ c ∈ K, ind H σ c ⟨F w, hlaw w⟩ = ⟨F w, hlaw w⟩ :=
    fun w c hc => Subtype.ext (funext fun x => hfix w c hc x)
  have hsm : ∀ w : A, (⟨F w, hlaw w⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := fun w =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun c hc => hfix' w c hc)
  have hT : ∀ w : A, (⟨⟨F w, hlaw w⟩, hsm w⟩ : smoothPart (ind H σ)) ∈ fixed (smInd H σ) K := by
    intro w c
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (hfix' w c c.2)
  let T : A →ₗ[ℂ] fixed (smInd H σ) K :=
    { toFun := fun w => ⟨⟨⟨F w, hlaw w⟩, hsm w⟩, hT w⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (Subtype.ext (map_add F a b)))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (Subtype.ext (map_smul F c a))) }
  have hS1 : S 1 := ⟨1, by simp [K.one_mem]⟩
  have hF1 : ∀ w : A, F w 1 = w := by
    intro w
    rw [F_pos w 1 hS1]
    refine (key 1 _ ?_ w w.2).trans (by simp)
    have h3 := K.inv_mem (pick_spec 1 hS1)
    simpa using h3
  have hinj : Function.Injective T := by
    intro a b hab
    have h4 : F a = F b := congrArg (fun t : fixed (smInd H σ) K => t.1.1.1) hab
    exact Subtype.ext (by rw [← hF1 a, ← hF1 b, h4])
  exact Module.Finite.of_injective T hinj

theorem isAdmissible_of_parInd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} (d : Fin s → ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth ρ → IsAdmissible (parInd (GlobalTheory.CompanionTheory.BZInd.stdE d) ρ) → IsAdmissible ρ := by
  intro k _ _ _ _ s d W _ _ ρ hρ hA
  refine ⟨hρ, fun L hLo _ => ?_⟩
  let δ := deltaHalf k fun a => Fin (d a)
  let L' : Subgroup (Levi k fun a => Fin (d a)) := L ⊓ δ.ker
  have hL' : IsOpen (L' : Set (Levi k fun a => Fin (d a))) :=
    hLo.inter (isSmoothChar_deltaHalf k)
  have hpre := hL'.preimage (ProdIrr.continuous_leviProj (GlobalTheory.CompanionTheory.BZInd.stdE d))
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hpre
  have h1 : (1 : GL (Fin (∑ a, d a)) k) ∈ U := by
    have h2 : (1 : parab k (GlobalTheory.CompanionTheory.BZInd.stdE d)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      simpa using L'.one_mem
    exact h2
  obtain ⟨m, -, hm⟩ :=
    (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (∑ a, d a)).mem_iff.1 (hU.mem_nhds h1)
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (∑ a, d a) m
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (∑ a, d a) m
  refine finiteDimensional_of_smInd_fixed (parab k (GlobalTheory.CompanionTheory.BZInd.stdE d))
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (∑ a, d a) m) hKo
    ((twist ρ δ).comp (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d))) (fixed ρ L) ?_ (hA.2 _ hKo hKc)
  intro c hc w hw
  have hcL : leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c ∈ L' := by
    have h2 : c ∈ Subtype.val ⁻¹' U := hm hc
    rw [hUe] at h2
    exact h2
  have hδ : δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) = 1 := MonoidHom.mem_ker.1 hcL.2
  have hw' := hw ⟨_, hcL.1⟩
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at hw'
  show ((δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) : ℂˣ) : ℂ) •
    ρ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) w = w
  rw [hδ, Units.val_one, one_smul]
  exact hw'

end GlobalTheory.CompanionTheory.LeviAdm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDual
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem invariant_forms_separate_fixed :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J,
      (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  intro G _ _ _ J hJ V _ _ π hπ u hu hl
  obtain ⟨E, -, hfix, -, hinv, -⟩ := GlobalTheory.T.compact_fixed_vector_projection G J hJ V π hπ
  by_contra hne
  have hex : ∃ l0 : Module.Dual ℂ V, l0 u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 hall)
  obtain ⟨l0, hl0⟩ := hex
  have hzero : (l0 ∘ₗ E) u = 0 := by
    refine hl (l0 ∘ₗ E) fun x hx => ?_
    rw [LinearMap.comp_assoc, hinv x hx]
  apply hl0
  simpa [hfix u hu] using hzero

end GlobalTheory.CompanionTheory.CompactAvg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cotangent_independent_unit_mul {R : Type} [CommRing R] [IsLocalRing R] {d : ℕ}
    (a a' : Fin d → R) (w : Rˣ) (h : ∀ j, a' j = w * a j)
    (hl : LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R))) :
    LinearIndependent (ResidueField R) (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) := by
  classical
  have hmem : ∀ j, a' j ∈ maximalIdeal R ↔ a j ∈ maximalIdeal R := fun j => by
    rw [h j]; exact Ideal.unit_mul_mem_iff_mem _ w.isUnit
  let e : {j : Fin d // a j ∈ maximalIdeal R} ≃ {j : Fin d // a' j ∈ maximalIdeal R} :=
    Equiv.subtypeEquivRight (fun j => (hmem j).symm)
  have hu : IsUnit (IsLocalRing.residue R (w : R)) := w.isUnit.map _
  have key : (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) =
      (fun j => hu.unit • ((maximalIdeal R).toCotangent ⟨_, (e.symm j).2⟩ : CotangentSpace R)) := by
    funext j
    obtain ⟨j, hj⟩ := j
    have hj' : a j ∈ maximalIdeal R := (hmem j).1 hj
    have hsub : (⟨a' j, hj⟩ : maximalIdeal R) = (w : R) • (⟨a j, hj'⟩ : maximalIdeal R) :=
      Subtype.ext (by simp [h j])
    show (maximalIdeal R).toCotangent ⟨a' j, hj⟩ = hu.unit • (maximalIdeal R).toCotangent ⟨a j, hj'⟩
    rw [hsub, map_smul, Units.smul_def, IsUnit.unit_spec, ← IsLocalRing.ResidueField.algebraMap_eq,
      algebraMap_smul]
  rw [key]
  exact (hl.units_smul (fun _ => hu.unit)).comp e.symm e.symm.injective

theorem germ_chart_eq {X : Scheme.{0}} {L : LB X} (s : L.Sec) (i c : L.ι) {x : X}
    (hi : x ∈ L.U i) (hc : x ∈ L.U c) :
    X.presheaf.germ (L.U i) x hi (s.f i) =
      X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩ (L.g i c : Γ(X, L.U i ⊓ L.U c)) *
        X.presheaf.germ (L.U c) x hc (s.f c) := by
  have e1 := congrArg (X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩) (s.compat i c)
  rw [map_mul] at e1
  have r1 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_left : L.U i ⊓ L.U c ⟶ L.U i).op (s.f i)) =
      X.presheaf.germ (L.U i) x hi (s.f i) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_left) x ⟨hi, hc⟩ (s.f i)
  have r2 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_right : L.U i ⊓ L.U c ⟶ L.U c).op (s.f c)) =
      X.presheaf.germ (L.U c) x hc (s.f c) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_right) x ⟨hi, hc⟩ (s.f c)
  rw [← r1, ← r2]
  exact e1

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (b : Fin n → L.Sec)
    (c : L.ι) : (∑ p, a p • b p).f c = ∑ p, resG X le_top (a p) * (b p).f c := by
  let φ : L.Sec →+ Γ(X, L.U c) :=
    { toFun := fun s => s.f c, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact (map_sum φ (fun p => a p • b p) Finset.univ).trans (Finset.sum_congr rfl fun p _ => rfl)

theorem resG_algebraMap (Y : Var ℂ) (V : Y.X.Opens) (a : ℂ) :
    resG Y.X (le_top : V ≤ ⊤) (algebraMap ℂ Γ(Y.X, ⊤) a) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V a := by
  rfl

theorem algX_smooth (Y : Var ℂ) {V : Y.X.Opens} (hV : IsAffineOpen V) :
    (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).Smooth := by
  haveI := Y.smooth_str
  have hsm : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
  have e : V ≤ Y.str ⁻¹ᵁ ⊤ := by simp
  have happ := HasRingHomProperty.appLE @Smooth Y.str hsm ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e
  have heq : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V =
      (Y.str.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    ext a
    rw [← resG_algebraMap, GlobalTheory.ProjVar.Var.algebraMap_Γ]
    rfl
  rw [heq]
  exact (RingHom.Smooth.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
    (Y.str.appLE ⊤ V e)).mpr happ

theorem bertini_on_affine (Y : Var ℂ) (L : LB Y.X) (n d : ℕ) (b : Fin n → L.Sec) (c : L.ι)
    {V : Y.X.Opens} (hV : IsAffineOpen V) (hVc : V ≤ L.U c) :
    ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧
      ∀ u : Fin d × Fin n → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (x : Y.X) (hx : x ∈ V), (∃ p, x ∈ nonzeroLocus (b p)) →
        LinearIndependent (ResidueField (Y.X.presheaf.stalk x))
          (fun j : {j : Fin d // Y.X.presheaf.germ (L.U c) x (hVc hx)
              ((∑ p, algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)) • b p).f c) ∈
                maximalIdeal (Y.X.presheaf.stalk x)} =>
            ((maximalIdeal (Y.X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
              CotangentSpace (Y.X.presheaf.stalk x))) := by
  classical
  letI : Algebra ℂ Γ(Y.X, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).toAlgebra
  haveI : Algebra.Smooth ℂ Γ(Y.X, V) := algX_smooth Y hV
  obtain ⟨Q, hQ, hQu⟩ := GlobalTheory.bertini_cotangent_independent ℂ Γ(Y.X, V)
    (fun p : Fin n => resG Y.X hVc ((b p).f c)) d
  refine ⟨Q, hQ, fun u hu x hx hnz => ?_⟩
  have hgres : ∀ {U W : Y.X.Opens} (h : W ≤ U) (hxW : x ∈ W) (z : Γ(Y.X, U)),
      Y.X.presheaf.germ W x hxW (resG Y.X h z) = Y.X.presheaf.germ U x (h hxW) z :=
    fun h hxW z => Y.X.presheaf.germ_res_apply (homOfLE h) x hxW z
  have hgs : ∀ {U : Y.X.Opens} (hxU : x ∈ U) (z : Γ(Y.X, U)),
      gs (𝟙 Y.X) x U z = Y.X.presheaf.germ U x hxU z := by
    intro U hxU z
    simp [gs, hxU]
    rfl
  let x' : V := ⟨x, hx⟩
  let q := (hV.primeIdealOf x').asIdeal
  letI : Algebra Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) :=
    TopCat.Presheaf.algebra_section_stalk Y.X.presheaf x'
  haveI := hV.isLocalization_stalk x'
  have hf : ∃ p, resG Y.X hVc ((b p).f c) ∉ q := by
    obtain ⟨p, hp⟩ := hnz
    obtain ⟨k, hk, hunit⟩ := (mem_nonzeroLocus (b p) x).1 hp
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_sec L (b p) k c x hk (hVc hx)] at hunit
    have hu2 : IsUnit (Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c)) := by
      rw [← hgs (hVc hx)]; exact isUnit_of_mul_isUnit_right hunit
    refine ⟨p, fun hmem => ?_⟩
    have h0 := (GlobalTheory.residue_algebraMap_eq_zero_iff_mem (R := Y.X.presheaf.stalk (x' : Y.X)) q _).2 hmem
    have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
        Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
    rw [e2, IsLocalRing.residue_eq_zero_iff] at h0
    exact h0 hu2
  have hLI := hQu u hu q (Y.X.presheaf.stalk (x' : Y.X)) hf
  refine cotangent_independent_unit_mul _ _ 1 (fun j => ?_) hLI
  rw [Units.val_one, one_mul, sum_smul_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.smul_def, map_mul, map_mul]
  have e1 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (algebraMap ℂ Γ(Y.X, V) (u (j, p))) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) (resG Y.X le_top (algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)))) := by
    show Y.X.presheaf.germ V x hx (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V (u (j, p))) = _
    rw [← resG_algebraMap, hgres, hgres]
  have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
  rw [e1, e2]

theorem bertini_cotIndep : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∀ (n d : ℕ) (b : Fin n → L.Sec), (⨆ j, nonzeroLocus (b j) = ⊤) → ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧ ∀ C : Fin d → Fin n → ℂ, MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 → CotIndep (fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j) := by
  intro Y L hL n d b hb
  classical
  haveI : CompactSpace Y.X := (Var.isNoetherian_X Y).toCompactSpace
  obtain ⟨m, V, c, hVa, hVc, hcov⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_affine_chart_cover L hL
  choose Q hQ hQu using fun k : Fin m => bertini_on_affine Y L n d b (c k) (hVa k) (hVc k)
  refine ⟨∏ k, Q k, Finset.prod_ne_zero_iff.2 fun k _ => hQ k, fun C hC => ?_⟩
  intro x i hx
  have hCk : ∀ k, MvPolynomial.eval (fun p => C p.1 p.2) (Q k) ≠ 0 := by
    intro k
    rw [map_prod] at hC
    exact Finset.prod_ne_zero_iff.1 hC k (Finset.mem_univ _)
  have hxV : x ∈ ⨆ k, V k := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hxV
  have hnz : ∃ p, x ∈ nonzeroLocus (b p) := by
    have : x ∈ ⨆ j, nonzeroLocus (b j) := by rw [hb]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have h6 := hQu k (fun p => C p.1 p.2) (hCk k) x hk hnz
  refine cotangent_independent_unit_mul _ _
    (IsUnit.map (ConcreteCategory.hom (Y.X.presheaf.germ (L.U i ⊓ L.U (c k)) x ⟨hx, hVc k hk⟩))
      (L.g i (c k)).isUnit).unit (fun j => ?_) h6
  rw [IsUnit.unit_spec]
  exact germ_chart_eq _ i (c k) hx (hVc k hk)

end GlobalTheory.CompanionTheory.KoszulCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.BZMir

theorem continuous_gpProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  intro k _ _ _ _ m j
  have hincl : Continuous (GlobalTheory.BZMir.Leib.hgpIncl k m j) := by
    apply continuous_induced_rng.2
    have hv : Continuous (fun h : GlobalTheory.BZMir.Leib.MirabolicParabolic k m j =>
        ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) := by
      first
        | exact continuous_subtype_val.comp continuous_subtype_val
        | fun_prop
    exact hv
  have hlevi := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ _ _
    (GlobalTheory.BZMir.Leib.eGP m j)).2.2.2.2.2.1
  have hblock := hlevi.comp hincl
  unfold GlobalTheory.BZMir.Leib.gpProj
  rw [MonoidHom.coe_prod]
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_apply false).comp hblock
  · apply continuous_induced_rng.2
    exact (continuous_apply true).comp hblock

end GlobalTheory.CompanionTheory.BZMir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormula
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibGP

section SlopeTestRemainingChoices

variable (k : Type) [Field k]

theorem blockIndex_false (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨false, a⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin j) :
    eGP m j ⟨true, Fin.castSucc b⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨true, b⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem glEmbMat_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

end SlopeTestRemainingChoices

theorem gpProj_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  intro k _ _ _ _ m j p hp hp'
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  · apply Subtype.ext
    apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]

end GlobalTheory.CompanionTheory.LeibGP

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.GpUnip

theorem mirUin_entry (k : Type) [Field k] (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n)
    (a b : Fin (n + 1)) (hb : b ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b := by
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hu)
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) a b = _
  simp [GlobalTheory.BZMir.colMat, hb]

theorem gpProj_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) →
      (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  intro k _ _ _ _ m j u hu
  have key : ∀ a b : Fin (m + j + 1), b ≠ Fin.last (m + j) →
      (((u : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b =
        (1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b :=
    fun a b hb => GlobalTheory.CompanionTheory.GpUnip.mirUin_entry k (m + j) _ hu a b hb
  have e_inj := (GlobalTheory.BZMir.Leib.eGP m j).injective
  constructor
  · ext i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) false i i'
    refine h.trans ((key _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j i')).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Units.val_one]
  · apply GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one
    ext i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) true (Fin.castSucc i) (Fin.castSucc i')
    have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i'⟩ ≠ Fin.last (m + j) :=
      fun hl => Fin.castSucc_ne_last i' ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).mp hl)
    refine h.trans ((key _ _ hne).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Fin.castSucc_inj, Units.val_one]

end GlobalTheory.CompanionTheory.GpUnip
end
end

