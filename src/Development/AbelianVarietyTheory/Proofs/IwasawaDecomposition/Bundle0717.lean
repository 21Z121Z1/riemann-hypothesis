import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem GlobalTheory.LamTie.cond0_primes_lowAll : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  intro D Z hZ hq P hP
  have hPr : Prime (GlobalTheory.ToricDenom.below P).asIdeal := (GlobalTheory.ToricDenom.below P).prime

  have key : ∀ n : ℕ, ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) →
      ((n : 𝓞 D.host.E) ∈ P.asIdeal) := by
    intro n hn
    have h1 : algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal := hn
    simpa using h1
  have key' : ∀ n : ℕ, ((n : 𝓞 D.host.E) ∈ P.asIdeal) →
      ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) := by
    intro n hn
    show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal
    simpa using hn
  unfold GlobalTheory.LamTie.cond0 at hP
  rcases hPr.dvd_or_dvd hP with h | h
  · have h2 := hPr.dvd_of_dvd_pow h
    rw [Ideal.dvd_span_singleton] at h2
    have h3 := key _ (by exact_mod_cast h2)
    push_cast at h3
    have hpr := P.isPrime
    rcases hpr.mem_or_mem h3 with h4 | h4
    · rcases hpr.mem_or_mem h4 with h5 | h5
      · rcases hpr.mem_or_mem h5 with h6 | h6
        · exact ⟨D.host.g 0, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
        · exact ⟨D.host.g 1, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
      · exact ⟨D.host.pde, by simp [GlobalTheory.HeightCounting.lowAll], h5⟩
    · exact ⟨D.host.pde', by simp [GlobalTheory.HeightCounting.lowAll], h4⟩
  · have hle : (GlobalTheory.ToricDenom.below Z.w0).asIdeal ≤ (GlobalTheory.ToricDenom.below P).asIdeal :=
      Ideal.le_of_dvd h
    have heq : (GlobalTheory.ToricDenom.below Z.w0).asIdeal = (GlobalTheory.ToricDenom.below P).asIdeal :=
      ((GlobalTheory.ToricDenom.below Z.w0).isMaximal).eq_of_le (GlobalTheory.ToricDenom.below P).isPrime.ne_top hle
    have hw : ((Z.q0 : ℕ) : 𝓞 D.host.E) ∈ Z.w0.asIdeal := hZ.places.referencePlaceOverPrime
    have hb : ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below Z.w0).asIdeal := by
      show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ Z.w0.asIdeal
      simpa using hw
    rw [heq] at hb
    refine ⟨Z.q0, ?_, key _ hb⟩
    rw [hq]
    simp [GlobalTheory.HeightCounting.lowAll, lowPr]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtInteriorPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

section Empty

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isCone_empty (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Subsingleton X] : ConeO H φ X 0 Fin.elim0 := by
  have hB : ∀ β : LinearMap.BilinForm ℤ X, β = 0 := fun β =>
    LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  have hz : ∀ β : LinearMap.BilinForm ℤ X, φ.evalZ β = 0 := fun β => φ.eval_of_subsingleton _
  refine ⟨fun i => i.elim0, fun i => i.elim0, ?_, fun c _ => ?_, ?_⟩
  · have : Subsingleton (balForms H.bar X) := ⟨fun a b => Subtype.ext ((hB a).trans (hB b).symm)⟩
    exact ⟨0, Module.Basis.empty _, fun i => i.elim0⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact φ.eval_of_subsingleton _
  · refine ⟨1, 0, one_pos, fun i => i.elim0, fun β _ _ => by simp [hz], fun β _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩
    simp [hB β]

theorem inCone_empty {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) [Subsingleton Dg.X] :
    InCone Dg (m := 0) Fin.elim0 := by
  intro W _ _ _ _ ϖ _ f be _ _
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  ext a b
  rw [Subsingleton.elim a 0]
  simp

end Empty

end GlobalTheory.GenFan

namespace GlobalTheory.GenFan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem isOpenImmersion_j (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  unfold Model.j
  have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
      infer_instance
    infer_instance
  have := Y.jQ_open
  infer_instance

theorem coneAt_j (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (w : Xo.XF c) :
    GlobalTheory.GenFan.ConeAt (ConeO H φ) Y (Y.j w) := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsProper Y.s := projProper _ _ _ Y.proj
  obtain ⟨R, _, _, _, ξ, hR, hξ, he, hu, hsp⟩ := GlobalTheory.T.exists_complete_local_etale_neighbourhood c.F Y.X Y.s inferInstance Y.normal (Y.j w)
  have hj := isOpenImmersion_j Y
  have hr : Set.range ξ ⊆ Set.range Y.j := fun _ ⟨p, hp⟩ =>
    hp ▸ (hsp p).mem_open Y.j.isOpenEmbedding.isOpen_range ⟨w, rfl⟩
  obtain ⟨t, m, hpol, hth, hab⟩ := GlobalTheory.T.exists_semi_abelian_polarized Y R ξ hR hr
  obtain ⟨P, hP, hX⟩ := GlobalTheory.T.exists_uniformization_abelian R t hR hpol hth hab
  exact ⟨R, _, _, _, ξ, t, m, P, 0, Fin.elim0, hR, hξ, he, hu, hP, isCone_empty H φ _, inCone_empty _⟩

end GlobalTheory.GenFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysOfLinearIndependentIntForms
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace ConeMatch

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem coef_eq {n : ℕ} {P : Fin n → V} (hP : LinearIndependent ℝ P) {a b : Fin n → ℝ}
    (h : ∑ i, a i • P i = ∑ i, b i • P i) : a = b := by
  have := Fintype.linearIndependent_iff.1 hP (a - b) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i; exact sub_eq_zero.1 (this i)

theorem exists_pos_of_sum_eq_one {n : ℕ} (f : Fin n → ℝ) (h : ∑ i, f i = 1) : ∃ i, 0 < f i := by
  by_contra hc
  push_neg at hc
  have : ∑ i, f i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
  linarith

theorem match_vec {k m : ℕ} (P : Fin k → V) (Q : Fin m → V) (hP : LinearIndependent ℝ P)
    (hQ : LinearIndependent ℝ Q) (t : Fin k → ℝ) (c : Fin m → ℝ) (ht : ∀ i, 0 < t i) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ i, t i • P i = ∑ j, c j • Q j)
    (hPQ : ∀ i, ∃ a : Fin m → ℝ, (∀ j, 0 ≤ a j) ∧ P i = ∑ j, a j • Q j)
    (hQP : ∀ j, 0 < c j → ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ Q j = ∑ l, b l • P l) :
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ P i = d • Q j) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ P i = d • Q j ∧ c j = t i * d) := by
  choose D hD0 hD using hPQ
  have hQP' : ∀ j, ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ (0 < c j → Q j = ∑ l, b l • P l) := fun j => by
    by_cases h : 0 < c j
    · obtain ⟨b, hb, e⟩ := hQP j h
      exact ⟨b, hb, fun _ => e⟩
    · exact ⟨0, fun _ => le_rfl, fun h' => absurd h' h⟩
  choose E hE0 hE using hQP'

  have hcD : ∀ j, c j = ∑ i, t i * D i j := by
    have h1 : ∑ j, c j • Q j = ∑ j, (∑ i, t i * D i j) • Q j := by
      rw [← hsum]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (coef_eq hQ h1)
  have hDz : ∀ i j, ¬ 0 < c j → D i j = 0 := fun i j h => by
    have h0 : c j = 0 := le_antisymm (not_lt.1 h) (hc j)
    rw [hcD j] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (ht i).le (hD0 i j)).1 h0 i
      (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (ht i).ne'
  have hDQ : ∀ i j, D i j • Q j = D i j • ∑ l, E j l • P l := fun i j => by
    by_cases h : 0 < c j
    · rw [← hE j h]
    · simp [hDz i j h]
  have hDE : ∀ i l, ∑ j, D i j * E j l = if i = l then 1 else 0 := by
    intro i l
    have h1 : ∑ l, (if i = l then (1 : ℝ) else 0) • P l = ∑ l, (∑ j, D i j * E j l) • P l := by
      rw [show ∑ l, (if i = l then (1 : ℝ) else 0) • P l = P i by simp [ite_smul]]
      conv_lhs => rw [hD i]
      simp only [hDQ, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hP h1) l).symm
  have hED : ∀ j, 0 < c j → ∀ j', ∑ l, E j l * D l j' = if j = j' then 1 else 0 := by
    intro j hj j'
    have h1 : ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = ∑ j', (∑ l, E j l * D l j') • Q j' := by
      rw [show ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = Q j by simp [ite_smul]]
      conv_lhs => rw [hE j hj]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hQ h1) j').symm
  have single : ∀ i j, 0 < D i j * E j i → 0 < c j ∧ 0 < D i j ∧ P i = D i j • Q j := by
    intro i j hpos
    have hcj : 0 < c j := by
      by_contra h
      rw [hDz i j h, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hEne : E j i ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    have hDpos : 0 < D i j := lt_of_le_of_ne (hD0 i j) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl _ hpos
    have hoff : ∀ j', j' ≠ j → D i j' = 0 := fun j' hj' => by
      have hle : E j i * D i j' ≤ ∑ l, E j l * D l j' :=
        Finset.single_le_sum (f := fun l => E j l * D l j') (fun l _ => mul_nonneg (hE0 j l) (hD0 l j'))
          (Finset.mem_univ i)
      rw [hED j hcj j', if_neg (Ne.symm hj')] at hle
      have h0 : E j i * D i j' = 0 := le_antisymm hle (mul_nonneg (hE0 j i) (hD0 i j'))
      exact (mul_eq_zero.1 h0).resolve_left hEne
    refine ⟨hcj, hDpos, ?_⟩
    rw [hD i, Finset.sum_eq_single j (fun j' _ hj' => by rw [hoff j' hj', zero_smul])
      (fun h => absurd (Finset.mem_univ j) h)]
  refine ⟨fun i => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj⟩ := exists_pos_of_sum_eq_one _ ((hDE i i).trans (if_pos rfl))
    obtain ⟨hcj, hd, e⟩ := single i j hj
    exact ⟨j, hcj, D i j, hd, e⟩
  · obtain ⟨l, hl⟩ := exists_pos_of_sum_eq_one _ ((hED j hj j).trans (if_pos rfl))
    have hl' : 0 < D l j * E j l := by rw [mul_comm]; exact hl
    obtain ⟨-, hd, e⟩ := single l j hl'
    have hEne : E j l ≠ 0 := fun h => by rw [h, zero_mul] at hl; exact lt_irrefl _ hl
    have hoff : ∀ i, i ≠ l → D i j = 0 := fun i hi => by
      have hle : D i j * E j l ≤ ∑ j'', D i j'' * E j'' l :=
        Finset.single_le_sum (f := fun j'' => D i j'' * E j'' l) (fun j'' _ => mul_nonneg (hD0 i j'') (hE0 j'' l))
          (Finset.mem_univ j)
      rw [hDE i l, if_neg hi] at hle
      have h0 : D i j * E j l = 0 := le_antisymm hle (mul_nonneg (hD0 i j) (hE0 j l))
      exact (mul_eq_zero.1 h0).resolve_right hEne
    refine ⟨l, D l j, hd, e, ?_⟩
    rw [hcD j, Finset.sum_eq_single l (fun i _ hi => by rw [hoff i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ l) h)]

end ConeMatch

section Forms

variable {X : Type} [AddCommGroup X]

theorem linearIndependent_toReal {n : ℕ} {p : Fin n → LinearMap.BilinForm ℤ X} (hp : LinearIndependent ℤ p) :
    LinearIndependent ℝ fun i => toReal (p i) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin n → ℤ), ∑ j, c j • p j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c h => by
    funext i
    exact Fintype.linearIndependent_iff.1 hp c (by simpa using h) i
  have := eq_zero_of_toReal_rel (u := p) (v := (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X)) hind
    (r := g) (s := 0) (by simpa using hg)
  exact fun i => congrFun this i

theorem cone_match_rays {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X)
    (δ : Fin m → LinearMap.BilinForm ℤ X) :
    LinearIndependent ℤ p → LinearIndependent ℤ δ →
    ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) →
      ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
      (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
      (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
      (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) :=
  fun hp hδ t c ht hc hsum hpδ hδp =>
    ConeMatch.match_vec (fun i => toReal (p i)) (fun j => toReal (δ j)) (linearIndependent_toReal hp)
      (linearIndependent_toReal hδ) t c ht hc hsum hpδ hδp

end Forms

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPq
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.OpenBaseDim

theorem dim_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ X j hoi _ _ k
  haveI := hoi
  have hcard : (U.X k).Ψ.card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_coe]; exact ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi (U.X k)
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.OpenBaseDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionLocalDataPreservedDivisionLatticeChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open Formalism.L2.Geo
open Formalism.L2.Geo.PadPkg renaming md → padMd
open Formalism.L2.Geo.CompatiblePlaces' renaming md → tiedMd

namespace GeoDivTr

section Gen
variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

set_option maxHeartbeats 4000000 in

@[reducible] def datBk {Lev : Type} (w : Dat (setDiv D N h) Lev) : Dat D Lev := { w with }

set_option maxHeartbeats 4000000 in

@[reducible] def mdlT {p : ℕ} [Fact p.Prime] {M : ℕ} {rk : DV.Emb D p → ℕ} (m : DV.Mdl D p M rk) : DV.Mdl (setDiv D N h) p M rk := { m with }

set_option maxHeartbeats 4000000 in

@[reducible] def locT {M j p : ℕ} (l : ModuliIntegralCharts.Loc D M j p) : ModuliIntegralCharts.Loc (setDiv D N h) M j p := { l with }

set_option maxHeartbeats 4000000 in

@[reducible] def padT {M j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    (P : PadPkg D M j Comp jC ng) : PadPkg (setDiv D N h) M j Comp jC ng :=
  { P with
    loc := fun p => locT N h (P.loc p)
    ex := fun p => { P.ex p with }
    locB := fun p hp => { P.locB p hp with }
    pbKF := fun p _ k => P.pbKF p k
    bc := fun p z => P.bc p z
    md := fun p _ la z => mdlT N h (padMd P p la z) }

set_option maxHeartbeats 4000000 in

@[reducible] def shimUT {G : DV.Geo D.what₂.LL} {Lev : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {w : Dat (setDiv D N h) Lev} (U : ShimU D G jC ng (datBk N h w)) : ShimU (setDiv D N h) G jC ng w :=
  { U with alg := { U.alg with }, pad := padT N h U.pad }

@[reducible] def wtB {j : ℕ} (w : WeightFamilies.Wt (setDiv D N h) j) : WeightFamilies.Wt D j := { w with }

set_option maxHeartbeats 8000000 in

@[reducible] def formsT {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
    {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
    (P : FormsPkg D G NW CompW algW PtY) :
    FormsPkg (setDiv D N h) G NW CompW (fun j => { algW j with }) PtY where
  KO := P.KO
  fKO := P.fKO
  nfKO := P.nfKO
  eO := P.eO
  kL := P.kL
  kL_eO := P.kL_eO
  Cusp := fun j w => P.Cusp j (wtB N h w)
  acgC := fun j w => P.acgC j (wtB N h w)
  modC := fun j w => P.modC j (wtB N h w)
  fdC := fun j w => P.fdC j (wtB N h w)
  modOC := fun j w => P.modOC j (wtB N h w)
  towC := fun j w => P.towC j (wtB N h w)
  cmp := fun j w c => P.cmp j (wtB N h w) c
  cmp_mem := fun j w c F => P.cmp_mem j (wtB N h w) c F
  cmp_cusp := fun j w c F => P.cmp_cusp j (wtB N h w) c F
  cmp_span := fun j h1 h2 w s hs => P.cmp_span j h1 h2 (wtB N h w) s hs
  cmp_indep := fun j w _ v hv => P.cmp_indep j (wtB N h w) v hv
  mulC := fun j w w' F F' => P.mulC j (wtB N h w) (wtB N h w') F F'
  cmp_mul := fun j w w' c F F' => P.cmp_mul j (wtB N h w) (wtB N h w') c F F'
  supN := fun j w => P.supN j (wtB N h w)
  supN_nonneg := fun j w => P.supN_nonneg j (wtB N h w)
  supN_eq_zero := fun j w => P.supN_eq_zero j (wtB N h w)
  supN_smul := fun j w => P.supN_smul j (wtB N h w)
  supN_add := fun j w => P.supN_add j (wtB N h w)
  l2NormAlt := fun j w => P.l2NormAlt j (wtB N h w)
  l2Norm_nonneg_bis := fun j w => P.l2Norm_nonneg_bis j (wtB N h w)
  l2Norm_eq_zero_iff := fun j w => P.l2Norm_eq_zero_iff j (wtB N h w)
  l2Norm_smul_alt := fun j w => P.l2Norm_smul_alt j (wtB N h w)
  l2Norm_add_le' := fun j w => P.l2Norm_add_le' j (wtB N h w)
  l2Norm_le_supNorm_alt := fun j w => P.l2Norm_le_supNorm_alt j (wtB N h w)
  Cu := P.Cu
  Xc := P.Xc
  Xc_lat := P.Xc_lat
  FJt := fun j c χ w => P.FJt j c χ (wtB N h w)
  acgF := fun j c χ w => P.acgF j c χ (wtB N h w)
  modF := fun j c χ w => P.modF j c χ (wtB N h w)
  sg := fun j c χ w => P.sg j c χ (wtB N h w)
  Pt := P.Pt
  pt66 := P.pt66
  vAtC := fun j la y w => P.vAtC j la y (wtB N h w)
  vAtC_zero := fun j la y w => P.vAtC_zero j la y (wtB N h w)
  vAtC_ne_bot := fun j la y w => P.vAtC_ne_bot j la y (wtB N h w)
  vAtC_add := fun j la y w => P.vAtC_add j la y (wtB N h w)
  vAtC_smul := fun j la y w => P.vAtC_smul j la y (wtB N h w)
  vAtC_mul := fun j la y w w' => P.vAtC_mul j la y (wtB N h w) (wtB N h w')
  thAll := fun j w => P.thAll j (wtB N h w)
  shortTh := fun j w => P.shortTh j (wtB N h w)

set_option maxHeartbeats 8000000 in

def famT {G : DV.Geo D.what₂.LL} {Lev : Type} (F : ShimFam D G Lev) : ShimFam (setDiv D N h) G Lev :=
  { F with
    U := fun w => shimUT N h (F.U (datBk N h w))
    forms := formsT N h F.forms }

set_option maxHeartbeats 4000000 in

theorem heq_mdlT {p : ℕ} [Fact p.Prime] {A A' : Type} {M M' : ℕ} {rk rk' : DV.Emb D p → ℕ}
    (f : A → DV.Mdl D p M rk) (g : A' → DV.Mdl D p M' rk') (hA : A = A') (hM : M = M') (hrk : rk = rk')
    (hfg : HEq f g) : HEq (fun z => mdlT N h (f z)) (fun z => mdlT N h (g z)) := by
  subst hA hM hrk
  obtain rfl := eq_of_heq hfg
  rfl

set_option maxHeartbeats 8000000 in

theorem geoTiedP_divTr {X : DivX D} {inK : X.Lev → ℕ → Prop} (hg : GeoTiedP X inK) :
    GeoTiedP (divTr N h X) inK := by
  obtain ⟨F, ePl, eC, hT, hJ, hC, hI, hL⟩ := hg
  refine ⟨famT N h F, ePl, eC, ⟨⟨hT.shv.lev, fun w hw => hT.shv.shv (datBk N h w) hw⟩,
    ⟨hT.pl.wt, hT.pl.jc, fun w hw => hT.pl.mp (datBk N h w) hw, ?_, fun w hw => hT.pl.curveM (datBk N h w) hw,
      fun w hw => hT.pl.degM (datBk N h w) hw, fun w hw => hT.pl.htMdl (datBk N h w) hw,
      fun w hw => hT.pl.htCurve (datBk N h w) hw⟩, ⟨fun j h1 h2 c => hT.geo.yv j h1 h2 c, fun j h1 h2 c => hT.geo.ybd j h1 h2 c,
      fun j h1 h2 c la => hT.geo.lw j h1 h2 c la⟩, hT.lev_κg⟩, hJ, hC,
    fun w w' hs hk hj hw hw' => hI (datBk N h w) (datBk N h w') hs hk hj hw hw', fun w M => hL (datBk N h w) M⟩
  intro w hw p _ la
  have hS := hT.shv.shv (datBk N h w) hw
  have hM : (X.shv w.S w.κ).N = (datBk N h w).N := by rw [show w.S = (datBk N h w).S from rfl, show w.κ = (datBk N h w).κ from rfl, hS]; rfl
  have hj : (X.shv w.S w.κ).j = (datBk N h w).j := by rw [show w.S = (datBk N h w).S from rfl, show w.κ = (datBk N h w).κ from rfl, hS]; rfl
  have hrk : DV.rkOf (DV.PsiOf D (X.jC p la)) (X.shv w.S w.κ).N (X.shv w.S w.κ).j =
      DV.rkOf (DV.PsiOf D (F.jC p (ePl p la))) (datBk N h w).N (datBk N h w).j := by
    rw [hT.pl.jc p la, hM, hj]
  exact heq_mdlT N h _ _ (hT.pl.mp (datBk N h w) hw p la) hM hrk (tiedMd hT.pl (datBk N h w) hw p la)

end Gen

end GeoDivTr

open GeoDivTr

set_option maxHeartbeats 8000000 in

theorem divT_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (Y : DivX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), DivT n Y → Nonempty (DivT (nchTTr w Z N h n) (divTr (D := w.D Z) N h Y)) := by
  intro B f T w Z Wt nch n Y N h d
  refine ⟨{ Qp := d.Qp, chr := { d.chr with }, loc := ?_, inK := d.inK, geo := geoTiedP_divTr (D := w.D Z) N h d.geo }⟩
  obtain ⟨h1, h2⟩ := d.loc
  exact ⟨h1, { h2 with }⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) :
    NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { x.o.N with ntw := N.tw, nexp := N.ex, nStage_trivialCharacter_coeff_eq := N.h0, nth := N.th, ntwbr := N.br, ntwbr_ind := N.hbr }

def oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : P.q.Over := ⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩

theorem dof_oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : (w.st (oTw x N).Z).toD7 = N.toD7 := rfl

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedFormsStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone H.bar X, ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  first | exact @GlobalTheory.RedTh.exists_adapted_siegel_basis | exact GlobalTheory.RedTh.exists_adapted_siegel_basis | (intros; apply GlobalTheory.RedTh.exists_adapted_siegel_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrameStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ fW.IsMap (X.X.presheaf.germ W z hz).hom fz := by
  first | exact @GlobalTheory.ShFam.StalkSpread.exists_affine_isMap | exact GlobalTheory.ShFam.StalkSpread.exists_affine_isMap | (intros; apply GlobalTheory.ShFam.StalkSpread.exists_affine_isMap <;> assumption)
end

