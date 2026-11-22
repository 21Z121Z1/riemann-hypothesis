import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerTriangularTwoBlockMulWeylTwoBlockEqTransvec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.VanishingBound

theorem keySec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hY.geo

theorem isSec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (la : AllWt.Weight (T.Q.Dw j)) (f : Rul Y.d.Xo₂ Y.d.c₂)
    (hf : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) :
    ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k) := by
  have hU := hY.unf σ hσ
  by_cases hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) la 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) la 0).1 (τ, i)
  · by_cases hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q
    · exact GlobalTheory.T.isSec_reading_decreasing_integer_exponents _ _ _ _ _ _ σ _ (Y.U σ) (keySec D T j Y e o hY σ hσ) hσ hU hpq _
        (AllWt.even_wtOf la 0) hdec f hf k
    · have hp : (T.Q.Dw j).p = 0 := by omega
      have hq : (T.Q.Dw j).q = 0 := by omega
      have hG : wtOf (T.Q.Dw j) la 0 = wtZ (fun _ => 0) 0 := by
        refine Prod.ext (funext fun x => ?_) ?_
        · simp only [wtOf, wtZ, hp, hq]
          split_ifs <;> first | (exfalso; omega) | simp
        · simp [wtOf, wtZ]
      rw [hG, AllWt.modelWt_wtZ]
      have hf' : f ∈ sec Y.d.Xo₂ Y.d.c₂ (fun _ => 0) 0 := by
        rw [← AllWt.secZ_nat, ← AllWt.exZ_wtZ, ← hG]
        exact hf
      exact hU.2.2.2.2.1 _ _ ⟨fun τ => fun a b _ => le_refl _, ⟨0, rfl⟩⟩ f hf' k
  · have hex : ∃ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ),
        (wtOf (T.Q.Dw j) la 0).1 (τ, m) < (wtOf (T.Q.Dw j) la 0).1 (τ, m + 1) := by
      by_contra hne
      push_neg at hne
      apply hdec
      intro τ i j' hij hj'
      revert hj'
      induction j', hij using Nat.le_induction with
      | base => intro _; exact le_refl _
      | succ n hn ih => intro hj'; exact (hne τ n hj').trans (ih (by omega))
    obtain ⟨τ, m, hm, hlt⟩ := hex
    have h0 : f = 0 := GlobalTheory.NonDomVanish.eq_zero_of_lt hf τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt
    subst h0
    rw [map_zero]
    exact ⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩

open scoped LaurentSeries in

theorem fjZero (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (la : AllWt.Weight (T.Q.Dw j)) (s) (hs : s ∈ vanBd TF.X Z la)
    (f : GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (hfs : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.suppOn Z) (hfsec : sec₀ TF.X Z _ f = H0.restr le_top s)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k)
    (hsec : ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k))
    (ξ) (hξ : ((Y.U σ).X k).IsIso ξ) (x) (hx : x ∈ ((Y.U σ).X k).dom) :
    ((Y.U σ).X k).fj (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) ξ 0 (rdU (Y.U σ) f k) x = 0 := by
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hU := hG.unf σ hσ
  letI : Algebra Y.d.c₂.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  have halg : ∀ x : Y.d.c₂.F, algebraMap Y.d.c₂.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)) :=
    fun _ => rfl
  obtain ⟨y, T₀, s', d, hbd, hd, hw⟩ :=
    GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) halg hσ hU k ξ hξ x hx _ _ TF.Y
  have hc : (algebraMap (PowerSeries ℂ) ℂ⸨X⸩).comp ((PowerSeries.C (R := ℂ)).comp σ) = algebraMap Y.d.c₂.F ℂ⸨X⸩ :=
    RingHom.ext fun t => (halg t).symm
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 none = 0 := rfl
  have hcoef : ∀ m ≤ (0:ℤ), (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff m = 0 := by
    intro m hm
    by_cases hZ : GlobalTheory.AllWt.LiesOn Z y
    · obtain ⟨v, hv, hval⟩ :=
        GlobalTheory.CuspOnTor.evR_mem_maximalIdeal _ _ _ _ _ _ TF.Y TF.X Z la s hs f hfsec (PowerSeries ℂ) ℂ⸨X⸩ _ y hc hZ hbd
      rw [hval]; exact GlobalTheory.CuspFrom.coeff_eq_zero hv hm
    · rw [hfs ℂ⸨X⸩ y ((GlobalTheory.AllWt.liesOff_iff Z y).2 hZ)]; rfl
  exact GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line _ _ _ _ _ ξ x s' d T₀ (fun j => (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff j) hsec
    (GlobalTheory.CuspFrom.freqNonneg _ hf1 hsec) hξ hx hd hcoef fun w hw' => ⟨(hw w hw').1, (hw w hw').2 _ hex _ f.2⟩

end GlobalTheory.HSApp.VanishingBound

namespace GlobalTheory.HSApp

open GlobalTheory.HSApp.VanishingBound in

theorem vanBd_le_space : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), vanBd TF.X Z la ≤ space TF.X Z Y.U la := by
  intro D T j Y e o hG hf Z TF la s hs
  obtain ⟨f, hfZ, hfs⟩ := GlobalTheory.T.exists_supportedRule_of_flagComponentSection _ _ _ _ _ _ _ TF.X Z (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) (H0.restr le_top s)
  have hsec := isSec D T j Y e o hG la f.1 f.2
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hcusp : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0) := by
    refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨f.2, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
    have h0 := fjZero D T j Y e o hG hf Z TF la s hs f hfZ hfs σ hσ k (hsec σ hσ k)
    have h3 := (GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ (hsec σ hσ k) (GlobalTheory.CuspFrom.isModerate _ hf1 (hsec σ hσ k)) h0).1.2
    exact ⟨⟨hsec σ hσ k, h3⟩, fun ξ hξ x hx => h0 ξ hξ x hx⟩
  exact ⟨⟨f.1, hcusp⟩, hfs⟩

end GlobalTheory.HSApp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOverFieldHasFlag
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

set_option autoImplicit false

open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (app_resM)

namespace GlobalTheory.Vert.Flag

theorem isFrame_biprod_top {X : Scheme.{0}} {F G : X.Modules} {ι κ : Type} [Fintype ι] [Fintype κ]
    {e : ι → Γ(F, ⊤)} {e' : κ → Γ(G, ⊤)} (he : IsFrame e) (he' : IsFrame e') :
    IsFrame (Sum.elim (fun i => (biprod.inl : F ⟶ F ⊞ G).app ⊤ (e i))
      fun i => (biprod.inr : G ⟶ F ⊞ G).app ⊤ (e' i)) := by
  refine isFrame_of_basis
      (fun W h => ((he.basis h).prod (he'.basis h)).map (QCoh.biprodSectionsEquiv F G W).symm) ?_
  rintro W h (i | i)
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl, Sum.elim_inl, ← app_resM]
    change (Limits.biprod.inl : F ⟶ F ⊞ G).app W _ + (Limits.biprod.inr : G ⟶ F ⊞ G).app W 0 = _
    simp [IsFrame.coe_basis]
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr, Sum.elim_inr, ← app_resM]
    change (Limits.biprod.inl : F ⟶ F ⊞ G).app W 0 + (Limits.biprod.inr : G ⟶ F ⊞ G).app W _ = _
    simp [IsFrame.coe_basis]

def ofRankZero {X : Scheme.{0}} {F : X.Modules} (h : IsVB F 0) : Vert.Flag F 0 where
  F _ := F
  ι _ := 𝟙 F
  isSubbundle _ := isSubbundle_of_isIso _
  isVB i := by rw [Fin.fin_one_eq_zero i]; exact h
  step := finZeroElim
  step_ι := finZeroElim
  isIso_last := IsIso.id F

theorem nonempty_of_isFrame_top {X : Scheme.{0}} : ∀ (n : ℕ) (F : X.Modules) (e : Fin n → Γ(F, ⊤)),
    IsFrame e → Nonempty (Vert.Flag F n) := by
  intro n
  induction n with
  | zero =>
    intro F e he
    have h := he.isVB
    rw [Fintype.card_fin] at h
    exact ⟨ofRankZero h⟩
  | succ n ih =>
    intro F e he
    obtain ⟨fl⟩ := ih (freeModule X (Fin n)) (freeFrame X (Fin n)) (isFrame_freeFrame X (Fin n))
    have hA : IsVB (freeModule X (Fin n) ⊞ structureModule X) (n + 1) :=
      (isVB_freeModule_fin X n).biprod (isVB_structureModule X)
    obtain ⟨flA⟩ := nonempty_extend X _ _ biprod.inl n
      (isSubbundle_inl (isVB_structureModule X)) hA fl
    have hf : IsFrame (Sum.elim
        (fun i => (biprod.inl : freeModule X (Fin n) ⟶ _ ⊞ structureModule X).app ⊤
          (freeFrame X (Fin n) i))
        fun i : Fin 1 => (biprod.inr : structureModule X ⟶ freeModule X (Fin n) ⊞ _).app ⊤
          ((fun _ : Fin 1 => (1 : Γ(X, ⊤))) i)) :=
      isFrame_biprod_top (isFrame_freeFrame X (Fin n)) (isFrame_one ⊤)
    exact ⟨flA.ofIso (hf.iso (he.comp_equiv finSumFinEquiv))⟩

theorem nonempty_of_field : ∀ (K : Type) [Field K] (E : (Spec (CommRingCat.of K)).Modules) (n : ℕ),
    GlobalTheory.VB.IsVB E n → Nonempty (Vert.Flag E n) := by
  intro K _ E n hE
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨U, e, hx, he⟩ := hE x
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
  exact nonempty_of_isFrame_top n E e he

end GlobalTheory.Vert.Flag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeImageComplPtsIn
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt

namespace GlobalTheory.Mean4O.CoverInt

theorem volume_image_compl_ptsIn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → (∀ W : X.Opens, Nonempty W → Function.Injective (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W)) → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (D : ℕ) (c : AlgChart p σ D), MeasureTheory.volume (c.e '' (c.e.source ∩ (ptsIn p σ U)ᶜ)) = 0 := by
  intro k _ X _ p σ hσ _ U hU D c
  have : IsDomain k := hσ.isDomain σ
  refine measure_mono_null ?_ (ae_iff.1 (SemiPosBir.ae_mem hσ c (U := U) ⟨_, hU⟩))
  rintro _ ⟨z, hz, rfl⟩ h
  have h₁ := h (c.e.map_source hz.1)
  rw [c.e.left_inv hz.1] at h₁
  exact hz.2 h₁

end GlobalTheory.Mean4O.CoverInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModularTransformationLevelStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_modular_transformation_level : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), wB N x (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * wB N (vact N x γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) := by
  first | exact @GlobalTheory.WpFam.wB_smul_transform | exact GlobalTheory.WpFam.wB_smul_transform | (intros; apply GlobalTheory.WpFam.wB_smul_transform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_parameter_strict_antitone : Size → Lifts fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * ((Fm.D x ι).R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  first | exact @GlobalTheory.QuoWt.weights_at_point | exact GlobalTheory.QuoWt.weights_at_point | (intros; apply GlobalTheory.QuoWt.weights_at_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartDependsOnLabelMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

set_option maxHeartbeats 1000000 in

theorem part_eq_of_congMod : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → GSum.part D z₁ z₂ a κ = GSum.part D z₁ z₂ a' κ := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hd D z₁ z₂ hq p _ c y h hy yy hl a a' ν ν' κ ha ha' hc
  subst hy
  obtain ⟨hon, hker⟩ := GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X hg hn hodd hi hE hT D.proj D.ε D.diag p
    (y (cPt p)) (D.lift c y h) yy hl
  obtain ⟨w, hw⟩ := hc
  obtain ⟨b, hb⟩ := hon (QuotientAddGroup.mk w)
  have hk : a - a' - D.m • b ∈ D.X.S.HH D.X.M (y (cPt p)) := by
    rw [← hker, AddMonoidHom.mem_ker]
    have e1 : yy (a - a' - D.m • b) = yy a - yy a' - D.m • yy b := by
      rw [map_sub, map_sub, map_nsmul]
    rw [e1, ha, ha', hb, hw]
    show ((QuotientAddGroup.mk (ν' + D.m • w) - QuotientAddGroup.mk ν' - D.m • QuotientAddGroup.mk w :
      ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))) = 0
    rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub]
    simp
  have hw' : wtChar D (D.X.S.TT D.X.M (y (cPt p))) a = wtChar D (D.X.S.TT D.X.M (y (cPt p))) a' := by
    ext t
    have ht : eStdBilin D.X.S.g _ (t : D.X.S.Gam) (a - a' - D.m • b) = 0 := t.2 _ hk
    have hsplit : D.m • a = D.m • a' + (D.m * D.m) • b + D.m • (a - a' - D.m • b) := by
      rw [mul_nsmul', ← smul_add, ← smul_add]
      congr 1
      abel
    have key : eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a) =
        eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a') + (D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b := by
      rw [hsplit]
      simp only [← eStdBilin_apply, map_add, map_nsmul, ht, smul_zero, add_zero]
    have hN : ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N)
        ((D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b) = 0 := by
      rw [map_nsmul, ← sq, ← D.sq, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    show ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a)) =
      ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a'))
    rw [key, map_add, hN, add_zero]
  simp only [part, hw']

end GlobalTheory.Poinc.GSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSizeStatement
section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_point_of_size : Size → WtPt := by
  first | exact @GlobalTheory.RefSum.DivWt.wtPt_of_size | exact GlobalTheory.RefSum.DivWt.wtPt_of_size | (intros; apply GlobalTheory.RefSum.DivWt.wtPt_of_size <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRule
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

theorem GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
        ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
          SiegelRule (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)
            (GlobalTheory.WeilSchrodinger.transD (cA σ) co) χS
            ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
            (omp.comp (MonoidHom.inl _ _)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS hχS rχS JB ξ hξ κ _ co hco ωd hωd omp htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS nT
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonalLagrangian_invariantForm_unique F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ co hco ν 𝓕 hν h𝓕 l hl hinv
  obtain ⟨hmem, hrule⟩ := GlobalTheory.T.siegelWeil_section_law_diagonalLagrangian F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ co hco ν 𝓕 hν h𝓕 χS hχS rχS
    ωd hωd omp htr p t hpt φ hφ
  show l (omp (p, 1) φ) = _
  rw [hc _ hmem, hrule, hc _ hφ]
  ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_condition_locus_isClopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  first | (exact @GlobalTheory.HTWeilLocus.weil_locus_clopen) | (exact GlobalTheory.HTWeilLocus.weil_locus_clopen) | (intros; apply GlobalTheory.HTWeilLocus.weil_locus_clopen  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB →
    ∀ (n : ℕ) (u : HolUnif A L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      ∀ (k : ℕ) (a b : Fin n → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm.mulVec (star b)).im : ℝ) : ℂ) / k) →
        Out.WeilIs A L k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | exact GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | (intros; apply GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsPullbackAffineClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem whiskerLeft_isPullback_affine_closed (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X)
    (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (hc : i' ≫ p = p' ≫ i) (hpb : IsPullback i'.left p'.left p.left i.left)
    [IsAffineHom p.left] [IsClosedImmersion i.left] :
    IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧
      IsClosedImmersion (E ◁ i).left := by
  have hP := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p
  have hI := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E i
  have hP' := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p'
  refine ⟨?_, MorphismProperty.of_isPullback hP.flip ‹_›, MorphismProperty.of_isPullback hI.flip ‹_›⟩
  have hout := hP'.flip.paste_horiz hpb
  refine IsPullback.of_right ?_ ?_ hP.flip
  · have h1 : (E ◁ i').left ≫ (snd E X').left = (snd E Z').left ≫ i'.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    have h2 : (E ◁ i).left ≫ (snd E X).left = (snd E Z).left ≫ i.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    rw [h1, h2]; exact hout
  · rw [← Over.comp_left, ← Over.comp_left, ← whiskerLeft_comp, ← whiskerLeft_comp, hc]

theorem glues_whiskerLeft : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧ IsClosedImmersion (E ◁ i).left ∧ GlobalTheory.PinchLift.Glues (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hg
  obtain ⟨h1, h2, h3⟩ := whiskerLeft_isPullback_affine_closed S E X X' Z Z' p i i' p' hc hpb
  refine ⟨h1, h2, h3, ?_⟩
  refine GlobalTheory.T.pullback_square_sections_glue_of_basis (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left
    {W | IsAffineOpen W ∧ ∃ V : X.left.Opens, IsAffineOpen V ∧ W ≤ (snd E X).left ⁻¹ᵁ V} ?_ ?_
  · intro W x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((snd E X).left x)) isOpen_univ
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ := (E ⊗ X).left.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((W ⊓ (snd E X).left ⁻¹ᵁ V : (E ⊗ X).left.Opens) : Set (E ⊗ X).left) from ⟨hx, hxV⟩)
      (W ⊓ (snd E X).left ⁻¹ᵁ V).isOpen
    exact ⟨W', ⟨hW', V, hV, fun y hy => (hle hy).2⟩, hxW', fun y hy => (hle hy).1⟩
  · rintro W ⟨hW, V, hV, hWV⟩
    exact GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange S E X X' Z Z' p i i' p' hE hc hpb hp hi hg V W hV hW hWV

end GlobalTheory.PinchLift
end

