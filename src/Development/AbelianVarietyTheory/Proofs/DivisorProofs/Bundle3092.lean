import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.IsomCalc

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
variable {L M : MLine p σ}

theorem isom_of_local {J : Type} (W : J → X.Opens) (hW : ∀ x, ∃ j, x ∈ W j) (a : J → M.B.ι)
    (b : J → L.B.ι) (ha : ∀ j, W j ≤ M.B.U (a j)) (hb : ∀ j, W j ≤ L.B.U (b j)) (u : ∀ j, Γ(X, W j)ˣ)
    (hu : ∀ (x : X) j j', x ∈ W j → x ∈ W j' → gm (𝟙 X) x (W j) (u j) =
      gm (𝟙 X) x _ (M.B.g (a j) (a j')) * (gm (𝟙 X) x _ (L.B.g (b j) (b j')))⁻¹ * gm (𝟙 X) x (W j') (u j'))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (W j) →
      M.φ.φ (a j) y = L.φ.φ (b j) y + logSq y (W j) (u j)) : L.Isom M := by
  let v (c : M.B.ι × L.B.ι) (j : J) : Γ(X, M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j)ˣ :=
    res (inf_le_inf inf_le_left (ha j)) (M.B.g c.1 (a j)) *
      (res (inf_le_inf inf_le_right (hb j)) (L.B.g c.2 (b j)))⁻¹ * res inf_le_right (u j)
  have hv (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (v c j) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    simp only [v, map_mul, map_inv, gm_res (𝟙 X) x _ hx]
  have key : ∀ {G : Type} [CommGroup G] (a b c d e : G), a * b * (c * d)⁻¹ * e = a * c⁻¹ * (b * d⁻¹ * e) := by
    intro G _ a b c d e
    simp only [mul_inv]
    ac_rfl
  have hg (c : M.B.ι × L.B.ι) : ∃ s : Γ(X, M.B.U c.1 ⊓ L.B.U c.2)ˣ, ∀ j, res inf_le_left s = v c j := by
    refine glue_unit _ _ _ (fun x hx => ?_) (v c) fun j j' x hx => ?_
    · obtain ⟨j, hj⟩ := hW x
      exact Opens.mem_iSup.2 ⟨j, hx, hj⟩
    · rw [hv c j x hx.1, hv c j' x hx.2, hu x j j' hx.1.2 hx.2.2,
        ← gm_cocycle M.φ.isLB (𝟙 X) x hx.1.1.1 (ha j hx.1.2) (ha j' hx.2.2),
        ← gm_cocycle L.φ.isLB (𝟙 X) x hx.1.1.2 (hb j hx.1.2) (hb j' hx.2.2), key]
  choose s hs using hg
  have hs' (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (s c) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    rw [← hv c j x hx, ← hs, gm_res (𝟙 X) x _ hx]
  refine ⟨⟨s⟩, (isGen_iff_germ _).2 fun x c c' hc hc' => ?_, fun a₀ b₀ y h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := hW x
    refine (hs' c j x ⟨hc, hj⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div' M.B L.B (𝟙 X) x c c' hc hc') (hs' c' j x ⟨hc', hj⟩)).symm)
    rw [← gm_cocycle M.φ.isLB (𝟙 X) x hc.1 hc'.1 (ha j hj),
      ← gm_cocycle L.φ.isLB (𝟙 X) x hc.2 hc'.2 (hb j hj), key]
  · obtain ⟨j, hj⟩ := hW (under y)
    have hj' : y ∈ ptsIn p σ (W j) := mem_ptsIn.2 hj
    have hy : y ∈ ptsIn p σ (M.B.U a₀ ⊓ L.B.U b₀ ⊓ W j) := by simp [*]
    have e : logSq y _ (s (a₀, b₀)) = logSq y _ (M.B.g a₀ (a j)) + -logSq y _ (L.B.g b₀ (b j)) +
        logSq y _ (u j) := by
      rw [← logSq_res inf_le_left hy, hs (a₀, b₀) j]
      simp only [v, logSq_mul hy, logSq_inv hy, logSq_res _ hy]
    have e₁ : _ = _ - logSq y _ (M.B.g a₀ (a j)) := M.φ.trans a₀ (a j) y h₁ (ptsIn_mono (ha j) hj')
    have e₂ : _ = _ - logSq y _ (L.B.g b₀ (b j)) := L.φ.trans b₀ (b j) y h₂ (ptsIn_mono (hb j) hj')
    have e₃ := hφ j y hj'
    change _ = _ + logSq y _ (s (a₀, b₀))
    linarith

theorem isom_of_chart (a : L.B.ι → M.B.ι) (ha : ∀ j, L.B.U j ≤ M.B.U (a j))
    (hg : ∀ (x : X) j j', x ∈ L.B.U j → x ∈ L.B.U j' →
      gm (𝟙 X) x _ (L.B.g j j') = gm (𝟙 X) x _ (M.B.g (a j) (a j')))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (L.B.U j) → M.φ.φ (a j) y = L.φ.φ j y) : L.Isom M :=
  isom_of_local L.B.U (exists_chart L.φ.isLB) a id ha (fun _ => le_rfl) (fun _ => 1)
    (fun x j j' h h' => by rw [map_one, map_one, ← hg x j j' h h', mul_one]; exact (mul_inv_cancel _).symm)
    fun j y h => by rw [logSq_one h, add_zero]; exact hφ j y h

theorem isom_refl (L : MLine p σ) : L.Isom L :=
  isom_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ => rfl

theorem isom_pull (h : L.Isom M) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (L.pull π hπ).Isom (M.pull π hπ) := by
  obtain ⟨w, hw, h⟩ := h
  refine isom_of_local (fun c : M.B.ι × L.B.ι => π ⁻¹ᵁ (M.B.U c.1 ⊓ L.B.U c.2))
    (fun x => ?_) (fun c _ => c.1) (fun c _ => c.2) (fun _ _ h => mem_pull.2 h.1)
    (fun _ _ h => mem_pull.2 h.2) (fun c => pullU π _ (w.s (c.1, c.2))) (fun x c c' hc hc' => ?_)
    fun c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.φ.isLB (π x)
    obtain ⟨b, hb⟩ := exists_chart L.φ.isLB (π x)
    exact ⟨(a, b), ha, hb⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g M.B π (𝟙 Y) x (fun _ => c.1) (fun _ => c'.1) (mem_pull.2 hc.1) (mem_pull.2 hc'.1))
      (gm_pull_g L.B π (𝟙 Y) x (fun _ => c.2) (fun _ => c'.2) (mem_pull.2 hc.2) (mem_pull.2 hc'.2)))).symm
    exact (gm_pull (U := M.B.U c.1 ⊓ L.B.U c.2) (𝟙 Y) π x hc (w.s (c.1, c.2))).trans
      ((gm_isGen hw (𝟙 Y ≫ π) x _ _ _ _ hc.1 hc'.1 hc.2 hc'.2).trans (congrArg (_ * ·)
        (gm_pull (U := M.B.U c'.1 ⊓ L.B.U c'.2) (𝟙 Y) π x hc' (w.s (c'.1, c'.2))).symm))
  · have hy' : PtsOver.map π hπ _ y ∈ ptsIn p σ (M.B.U c.1 ⊓ L.B.U c.2) := hy
    refine (M.φ.pull_φ π hπ _ y).trans ((h _ _ _ (mem_ptsIn_inf.1 hy').1 (mem_ptsIn_inf.1 hy').2).trans
      (congrArg₂ (· + ·) (L.φ.pull_φ π hπ (fun _ => c.2) y).symm ?_))
    exact congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_app π hπ _ _ y).symm

theorem isom_pull_tens (L M : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.tens M).pull π hπ).Isom ((L.pull π hπ).tens (M.pull π hπ)) :=
  isom_of_chart (fun j => (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2))
    (fun _ _ h => ⟨mem_pull.2 (mem_pull.1 h).1, mem_pull.2 (mem_pull.1 h).2⟩)
    (fun x j j' h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine ((gm_pull_g (CechPic.tens L.B M.B) π (𝟙 Y) x j j' h h').trans
        (gm_tens L.B M.B (𝟙 Y ≫ π) x _ _ e e')).trans (Eq.symm ?_)
      exact (gm_tens (L.B.pull π) (M.B.pull π) (𝟙 Y) x (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2)
        (fun _ => (j' PUnit.unit).1, fun _ => (j' PUnit.unit).2) ⟨mem_pull.2 e.1, mem_pull.2 e.2⟩
        ⟨mem_pull.2 e'.1, mem_pull.2 e'.2⟩).trans (congrArg₂ (· * ·)
          (gm_pull_g L.B π (𝟙 Y) x _ _ (mem_pull.2 e.1) (mem_pull.2 e'.1))
          (gm_pull_g M.B π (𝟙 Y) x _ _ (mem_pull.2 e.2) (mem_pull.2 e'.2))))
    fun j y _ => (congrArg₂ (· + ·) (L.φ.pull_φ π hπ _ y) (M.φ.pull_φ π hπ _ y)).trans
      ((L.tens M).φ.pull_φ π hπ j y).symm

theorem isom_pull_ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hu' : ∀ z, CInfAt (fun z => u (ptMap π hπ σ z)) z) :
    ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) hu') :=
  isom_of_chart (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' h h' => (gm_pull_g (LB.triv X) π (𝟙 Y) x j j' h h').trans ((map_one _).trans (map_one _).symm))
    fun j y _ => ((MLine.ofFun u hu).φ.pull_φ π hπ j y).symm

theorem isom_addFn (L : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) :
    (L.addFn u hu).Isom (L.tens (MLine.ofFun u hu)) :=
  isom_of_chart (fun c => (c, PUnit.unit)) (fun _ _ h => ⟨h, trivial⟩)
    (fun x c c' h h' => ((gm_tens L.B (LB.triv X) (𝟙 X) x (c, PUnit.unit) (c', PUnit.unit)
      ⟨h, trivial⟩ ⟨h', trivial⟩).trans ((congrArg (_ * ·) (map_one _)).trans (mul_one _))).symm)
    fun _ _ _ => rfl

theorem isom_pull_pull (L : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) {Z : Scheme.{0}} {r : Z ⟶ Sp k} (i : Z ⟶ Y)
    (hi : i ≫ q = r) (h₀ : (i ≫ π) ≫ p = r) : ((L.pull π hπ).pull i hi).Isom (L.pull (i ≫ π) h₀) :=
  isom_of_chart (fun J => fun _ => J PUnit.unit PUnit.unit)
    (fun _ _ h => mem_pull₂.2 (mem_pull.1 (mem_pull.1 h)))
    (fun x (J J' : PUnit → PUnit → L.B.ι) h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine (gm_pull_g (L.B.pull π) i (𝟙 Z) x J J' h h').trans
        ((gm_pull_g L.B π (𝟙 Z ≫ i) x (J PUnit.unit) (J' PUnit.unit) e e').trans ?_)
      rw [Category.assoc]
      exact (gm_pull_g L.B (i ≫ π) (𝟙 Z) x (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
        (mem_pull₂.2 (mem_pull.1 e)) (mem_pull₂.2 (mem_pull.1 e'))).symm)
    fun (J : PUnit → PUnit → L.B.ι) y _ => by
      refine (L.φ.pull_φ (i ≫ π) h₀ (fun _ => J PUnit.unit PUnit.unit) y).trans (Eq.trans ?_
        ((Weight.pull_φ (L.pull π hπ).φ i hi J y).trans (L.φ.pull_φ π hπ (J PUnit.unit) _)).symm)
      exact congrArg _ (Subtype.ext (by simp [PtsOver.map_val]))

end GlobalTheory.Mix.IsomCalc

open GlobalTheory.Mix.IsomCalc in

theorem GlobalTheory.Mix.isom_calculus : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q), (∀ A : MLine p σ, A.Isom A) ∧ (∀ A B : MLine p σ, A.Isom B → (A.pull π hπ).Isom (B.pull π hπ)) ∧ (∀ A B : MLine p σ, ((A.tens B).pull π hπ).Isom ((A.pull π hπ).tens (B.pull π hπ))) ∧ (∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) fun z => (hu _).pull π hπ)) ∧ (∀ (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (A.addFn u hu).Isom (A.tens (MLine.ofFun u hu))) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp k) (g : Z ⟶ Y) (hg : g ≫ q = r) (h : (g ≫ π) ≫ p = r) (A : MLine p σ), ((A.pull π hπ).pull g hg).Isom (A.pull (g ≫ π) h) :=
  fun _ _ _ _ _ _ _ π hπ => ⟨isom_refl, fun _ _ h => isom_pull h π hπ, fun A B => isom_pull_tens A B π hπ,
    fun u hu => isom_pull_ofFun u hu π hπ _, isom_addFn, fun _ _ g hg h A => isom_pull_pull A π hπ g hg h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncGenericPoints

theorem mem_vanishingIdeal_closure {X : Scheme.{0}} (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    (s : Γ(X, U.1)) (hs : ¬ IsUnit (X.presheaf.germ U.1 x hx s)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  by_contra hsq
  have hp : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact hsq
  have hq' : U.2.fromSpec q ∈ closure ({x} : Set X) := hq
  have hsp : x ⤳ U.2.fromSpec q := specializes_iff_mem_closure.2 hq'
  have hxs : x ∈ X.basicOpen s := hsp.mem_open (X.basicOpen s).isOpen hp
  exact hs ((X.mem_basicOpen s x hx).1 hxs)

theorem maximalIdeal_le_stalkId {X : Scheme.{0}} (x : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x := by
  intro a ha
  obtain ⟨V, hxV, f, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hle : W ≤ V := hWV
  have e : X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hle).op f) = X.presheaf.germ V x hxV f :=
    X.presheaf.germ_res_apply (homOfLE hle) x hxW f
  rw [← e] at ha ⊢
  generalize X.presheaf.map (homOfLE hle).op f = g at ha ⊢
  have hu : ¬ IsUnit (X.presheaf.germ W x hxW g) :=
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 ha)
  have hm := mem_vanishingIdeal_closure x ⟨W, hW⟩ hxW g hu
  have h1 : Ideal.map (X.presheaf.germ W x hxW).hom
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal ⟨W, hW⟩) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x :=
    le_iSup₂_of_le (f := fun (U : X.affineOpens) (hx : x ∈ U.1) =>
      Ideal.map (X.presheaf.germ U.1 x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U)) ⟨W, hW⟩ hxW le_rfl
  exact h1 (Ideal.mem_map_of_mem _ hm)

theorem coheight_eq_one_of_lSncAt {X : Scheme.{0}} {r : ℕ} (z : Fin r → X) (a : Fin r)
    (h : FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) (z a)) : Order.coheight (z a) = 1 := by
  obtain ⟨hreg, n, t, e, ht, hI⟩ := h
  have ha : z a ∈ (Closeds.closure {z a} : Closeds X) := subset_closure (Set.mem_singleton _)
  have hn : 1 ≤ n := (e ⟨a, ha⟩).pos
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) = Ideal.span {t (e ⟨a, ha⟩)} := by
    refine le_antisymm ((maximalIdeal_le_stalkId (z a)).trans (hI ⟨a, ha⟩).le) ?_
    rw [← ht.1]
    exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
  have hmin : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) ∈
      (Ideal.span {t (e ⟨a, ha⟩)}).minimalPrimes := by
    rw [← hm, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk (z a))
  have h2 := ringKrullDim_stalk_eq_coheight (z a)
  have h3 : (IsLocalRing.maximalIdeal (X.presheaf.stalk (z a))).height = Order.coheight (z a) :=
    WithBot.coe_eq_coe.1 (h1.trans h2)
  have h4 : ((n : ℕ∞)) = Order.coheight (z a) := WithBot.coe_eq_coe.1 (ht.2.trans h2)
  refine le_antisymm (h3 ▸ hle) ?_
  rw [← h4]
  exact_mod_cast hn

theorem exists_genericPoints : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  intro F _ X _ p D hp hs T hT
  haveI : QuasiCompact p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    infer_instance
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨m, C, hC, -⟩ := GlobalTheory.SncComponents.exists_compList_effCartier F X p D T hT
  have hL := GlobalTheory.SncLocal.lSncAt_of_snc' X T m C hT hC
  have hz : ∀ a, ∃ z : X, closure {z} = (C a : Set X) := fun a =>
    QuasiSober.sober (hC.1 a) (C a).isClosed
  choose z hz using hz
  have hCz : (fun a => (Closeds.closure {z a} : Closeds X)) = C :=
    funext fun a => SetLike.coe_injective (hz a)
  have hL' : ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
    rw [hCz]; exact hL
  have hco : ∀ a, Order.coheight (z a) = 1 := fun a => coheight_eq_one_of_lSncAt z a (hL' _)
  have hU : (T : Set X) = ⋃ a, closure {z a} := by
    rw [← hC.2.1]; simp only [hz]
  refine ⟨m, z, fun a b hab => hC.2.2 a b ?_, hco, hU, fun w hw hw1 => ?_, hL'⟩
  · rw [← hz, ← hz, hab]
  · have hw' : w ∈ (T : Set X) := hw
    rw [hU] at hw'
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hw'
    have hsp : z a ⤳ w := specializes_iff_mem_closure.2 ha
    refine ⟨a, ?_⟩
    by_contra hne
    have hlt : w < z a := lt_of_le_not_ge hsp fun h =>
      hne ((show w ⤳ z a from h).antisymm hsp).eq
    have := Order.coheight_strictAnti hlt (by rw [hco a]; exact ENat.natCast_lt_top 1)
    rw [hco a, hw1] at this
    exact lt_irrefl _ this

end GlobalTheory.SncGenericPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  first | exact @GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | exact GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | (intros; apply GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationDirectSummandStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareZeroLiftSystem_filtration_direct_summand : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ S : Sys I π s₀, (∃ N, IsCompl (S.K hI) N) ∧ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
  first | exact @GlobalTheory.LiftSys.summand_of_full | exact GlobalTheory.LiftSys.summand_of_full | (intros; apply GlobalTheory.LiftSys.summand_of_full <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkEvaluationRootOfUnityValueMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_evaluation_root_of_unity_value_member : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X : Setup F W i) (z : X.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X.M.Z.presheaf.stalk z →+* V) (Y : Type) [AddCommGroup Y] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Y) (𝔪 : UMem X z act V ev Y t δ) (zt : X.M.Z.presheaf.stalk z),
    X.M.stalkHom z zt = algebraMap X.o₁ X.Ω₁ X.S.ζ →
    algebraMap V (FractionRing V) (ev zt) = 𝔪.yK ⟨algebraMap X.o₁ X.Ω₁ X.S.ζ, X.S.R.algebraMap_mem _⟩ := by
  first | exact @GlobalTheory.Poinc.Sep.MemberZeta.algebraMap_ev_eq_yK | exact GlobalTheory.Poinc.Sep.MemberZeta.algebraMap_ev_eq_yK | (intros; apply GlobalTheory.Poinc.Sep.MemberZeta.algebraMap_ev_eq_yK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_cohomology_residue_field_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  first | exact @GlobalTheory.AbCoh.CohBaseChange.main | exact GlobalTheory.AbCoh.CohBaseChange.main | (intros; apply GlobalTheory.AbCoh.CohBaseChange.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1RankDescendsFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_h1_rank_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  first | exact @GlobalTheory.AbCoh.finrank_HO1_descend_field | exact GlobalTheory.AbCoh.finrank_HO1_descend_field | (intros; apply GlobalTheory.AbCoh.finrank_HO1_descend_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFirstChernGradedPullbackStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_first_chern_graded_pullback : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) = c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  first | exact @GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum | exact GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum | (intros; apply GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjectiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abVar_surjective_iff_ptMap_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left ↔ Function.Surjective (ptMap p) := by
  first | exact @GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | exact GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | (intros; apply GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveTwistedKernelAdditiveLineBundleFamily
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerSurj

theorem exists_point_geom : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S) (M : LB (A ⊗ Over.mk ξ).left), Fam A M → ∃ a : Over.mk ξ ⟶ A, Same A (abelian₂ A L) M a (𝟙 _) := by
  intro S A _ hA L hL hAmp K _ _ ξ M hM
  obtain ⟨A', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A ξ
  have := hA
  have : IsProper A.hom := IsAbelianScheme.proper
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  have := hA'
  have : IsCommMonObj A := IsAbelianScheme.comm
  have : IsCommMonObj A' := IsAbelianScheme.comm
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  have hAmp' : Out.RelAmple A' (L.pull φ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hAmp hφ.1
  have hs : 𝟙 (Sp K) ≫ ξ = ξ := Category.id_comp ξ
  have hN' : Fam A' (M.pull (BaseChange.toBase hφ hs)) := BaseChange.fam_toBase hφ hs hM
  obtain ⟨a', ha'⟩ := GlobalTheory.T.additiveLineBundle_eq_mumfordLambda_of_ample_algClosed K A' hA' (L.pull φ) hL' hAmp' _ hN'
  refine ⟨GlobalTheory.AbDual.pushP hφ hs a', ?_⟩

  obtain hsq := GlobalTheory.LamPull.exists_isSquare (G := A) (G' := A') (f := ξ) (φ := φ) hφ.1.w
  have hLam : (abelian₂ A L).IsLB := FullSiegel.isLB_lam hL
  have hLam' : (abelian₂ A' (L.pull φ)).IsLB := FullSiegel.isLB_lam hL'
  have eLam := (GlobalTheory.LamPull.lbIso_lam_pull hφ hL hL' (GlobalTheory.lbIso_self hL') hsq).symm
  have h0 := (same_iff hN'.isLB hLam' _ _).mp ha'
  have e1 : evc hN'.isLB (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) =
      GlobalTheory.CechPic.pull (BaseChange.toBase hφ hs) (evc hM.isLB (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _)) := by
    simp only [GlobalTheory.AbDual.evc]
    rw [show lift (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) = 𝟙 _ by simp,
      show lift (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _) = 𝟙 _ by simp,
      Over.id_left, Over.id_left, GlobalTheory.CechPic.pull_id]
    exact (GlobalTheory.CechPic.pull_id _).trans (GlobalTheory.CechPic.cls_pull hM.isLB _ hN'.isLB)
  rw [same_iff hLam hM.isLB]
  rw [BaseChange.pull_inj_iff (BaseChange.toBase hφ hs) (BaseChange.ofBase hφ hs)
    (BaseChange.ofBase_toBase hφ hs), ← e1]
  unfold BaseChange.toBase
  rw [pull_evc]
  refine Eq.trans (GlobalTheory.AbDual.evc_eq (f := φ) (g := φ) hsq.1 hsq.2 hLam hLam' eLam
      (s := (A' ⊗ 𝟙_ (Over (Sp K))).hom) (s₀ := (A' ⊗ 𝟙_ (Over (Sp K))).hom ≫ ξ)
      (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ a') _ _ ?_ ?_).symm h0.symm
  · rw [Over.comp_left, GlobalTheory.AbDual.lift_left_fst]; rfl
  · simp only [Over.comp_left]
    rw [← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
    simp [GlobalTheory.AbDual.pushP]

theorem surjective_twist_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → Surjective (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL hAmp T _ _ N hN H h _ hiff
  refine ⟨fun x => ?_⟩

  let Ω := AlgebraicClosure (T.left.residueField x)
  let p : Sp Ω ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) Ω)) ≫ T.left.fromSpecResidueField x
  let tpt : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p rfl
  have hMf := Fam.ev hN tpt
  obtain ⟨a, ha⟩ := exists_point_geom (Sp R) A hA L hL hAmp Ω (p ≫ T.hom) _ hMf
  have hs : Same A (abelian₂ A L) N a tpt := by
    rw [same_iff (FullSiegel.isLB_lam hL) hN.isLB]
    rw [same_iff (FullSiegel.isLB_lam hL) hMf.isLB] at ha
    rw [ha, GlobalTheory.AbDual.evc_ev hN.isLB]
    simp
  obtain ⟨z, hz⟩ := (hiff (Over.mk (p ≫ T.hom)) a tpt).mp hs
  have e : z.left ≫ (h ≫ snd A T).left = p := by
    rw [← Over.comp_left, ← Category.assoc, hz, lift_snd]
    rfl
  let q : Sp Ω := IsLocalRing.closedPoint Ω
  refine ⟨z.left.base q, ?_⟩
  have e2 : (h ≫ snd A T).left.base (z.left.base q) = p.base q :=
    (Scheme.Hom.comp_apply z.left (h ≫ snd A T).left q).symm.trans
      (congrArg (fun f : Sp Ω ⟶ T.left => f.base q) e)
  exact e2.trans ((Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _))

end GlobalTheory.TwistKerSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) := by
  first | exact @GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback | exact GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback | (intros; apply GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  first | exact @GlobalTheory.Mum.Conj.symLift_thTw | exact GlobalTheory.Mum.Conj.symLift_thTw | (intros; apply GlobalTheory.Mum.Conj.symLift_thTw <;> assumption)
end

