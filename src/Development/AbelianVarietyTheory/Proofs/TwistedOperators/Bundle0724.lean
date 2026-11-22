import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitEmbeddingValuedEqIntValuationInteger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0718
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0719
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0717
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0720
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetOfSelfDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLatCoset

theorem selfDual_eq : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.Col.conjPrime₂ P ≠ P → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → X = Y := by
  intro D V P X Y hP hX hY hXY hYX
  have hcc : ∀ s : 𝓞 D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.cc ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
    intro s
    show IsCMField.complexConj D.host.E (star (s : D.host.E)) = (s : D.host.E)
    exact star_star (s : D.host.E)
  have hcO : ∀ s : 𝓞 D.host.E, Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E s) = s := by
    intro s
    apply RingOfIntegers.ext
    show star (star (s : D.host.E)) = (s : D.host.E)
    exact star_star _
  have key : ∀ (s : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E),
      ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) (s • v) y =
        ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v (Formalism.L2.Col.cO D.host.E s • y) := by
    intro s v y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 : (s • v) a = (s : D.host.E) * v a := rfl
    have e2 : (Formalism.L2.Col.cO D.host.E s • y) b = ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b := rfl
    have e3 : ReciprocityTheory.ChartRestriction.G.FD.cc (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b) =
        (s : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.cc (y b) := by
      rw [← hcc s]
      exact map_mul (IsCMField.complexConj D.host.E) _ _
    rw [e1, e2, e3]
    ring
  have hne : P.asIdeal ≠ (Formalism.L2.Col.conjPrime₂ P).asIdeal := fun h =>
    hP (IsDedekindDomain.HeightOneSpectrum.ext h.symm)
  have hcop : P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne P.isMaximal (Formalism.L2.Col.conjPrime₂ P).isMaximal hne
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal)
  have hsc : Formalism.L2.Col.cO D.host.E s ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, hcO]
    exact hs
  have incl : ∀ X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → Y ≤ X := by
    intro X Y hX hY hXY hYX l hl
    have h1 : t • l ∈ X := hYX (Submodule.smul_mem_smul ht hl)
    have h2 : s • l ∈ X := by
      rw [← hX]
      intro x hx
      have hx' : Formalism.L2.Col.cO D.host.E s • x ∈ Y := hXY (Submodule.smul_mem_smul hsc hx)
      obtain ⟨n, hn⟩ := (hY l).2 hl _ hx'
      exact ⟨n, by rw [key]; exact hn⟩
    have e : l = s • l + t • l := by rw [← add_smul, hst, one_smul]
    rw [e]
    exact X.add_mem h2 h1
  exact le_antisymm (incl Y X hY hX hYX hXY) (incl X Y hX hY hXY hYX)

theorem latG_mul_levG : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (x κ : GA D (Wc D i)),
    κ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) → latG (Wc D i) (x * κ) = latG (Wc D i) x := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i x κ hκ
  have hκ' : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ :=
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  have hS := GlobalTheory.DictMove.latGHat_eq (hL.βW i) hκ'
  ext v
  rw [(GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).1, (GlobalTheory.MarkCoset.latG_spec D _ x).1,
    (GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).2, (GlobalTheory.MarkCoset.latG_spec D _ x).2]
  constructor
  · rintro ⟨y, hy, hyz⟩
    refine ⟨(finHom (Wc D i) κ).1.mulVec y, ?_, ?_⟩
    · rw [← hS]
      exact ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).2 ⟨y, hy, rfl⟩
    · rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  · rintro ⟨y, hy, hyz⟩
    rw [← hS] at hy
    obtain ⟨y', hy', rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).1 hy
    exact ⟨y', hy', by rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩

theorem exists_coset_of_selfDual : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    ∀ (g : GA D (Wc D i)) (L' : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)),
    P.asIdeal • latG (Wc D i) g ≤ L' → (Formalism.L2.Col.conjPrime₂ P).asIdeal • L' ≤ latG (Wc D i) g →
    (∀ v : Fin (Wc D i).rank → D.host.E, (∀ y ∈ L', ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(Wc D i).gram.transpose) v y) = n) ↔ v ∈ L') →
    (L' ⊓ latG (Wc D i) g).toAddSubgroup.relIndex (latG (Wc D i) g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a ∈ Rc, latG (Wc D i) (g * a) = L' ∧ ∃ (e : AE D) (a₀ : GA D (Wc D i)), Formalism.L2.NTheta.IsIdemAt e P ∧
      SuppAt e (Wc D i) a₀ ∧ a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) ∧ latG (Wc D i) (g * a₀) = L' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hα hRc g L' h1 h2 hsd hidx
  obtain ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ := hα
  have hP : Formalism.L2.Col.conjPrime₂ P ≠ P := by
    intro h
    apply hso.1
    rw [Formalism.L2.Col.conjIdeal_asIdeal, h]
  obtain ⟨a₀, ha₀, hT, hT2⟩ := GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split D (Wc D i) P e ϖ k g (L' ⊓ latG (Wc D i) g) he hϖ1 hϖ2
    (le_inf h1 Submodule.smul_le_right) inf_le_right hidx
  obtain ⟨a, ha, hK⟩ := GlobalTheory.T.exists_coset_rep_hecke_element_principal_level D R hL hF i P k α Rc e ϖ a₀ hso ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ hRc he hϖ1 hϖ2 ha₀
  have hTL : latG (Wc D i) (g * a₀) = L' := by
    refine selfDual_eq D (Wc D i) P _ _ hP (GlobalTheory.Member.latG_selfDual D (Wc D i) (g * a₀) _ rfl).2.2 hsd ?_ ?_
    · refine le_trans ?_ (inf_le_left : L' ⊓ latG (Wc D i) g ≤ L')
      rw [← hT]
      exact le_inf Submodule.smul_le_right hT2
    · refine le_trans ?_ (inf_le_left : latG (Wc D i) (g * a₀) ⊓ latG (Wc D i) g ≤ _)
      rw [hT]
      exact le_inf Submodule.smul_le_right h2
  have hga : latG (Wc D i) (g * a) = latG (Wc D i) (g * a₀) := by
    have := latG_mul_levG D R hL i (g * a) (a⁻¹ * a₀) hK
    rw [← this, mul_assoc, mul_inv_cancel_left]
  exact ⟨a, ha, hga.trans hTL, e, a₀, he, ha₀.2.1, hK, hTL⟩

end GlobalTheory.HeckeLatCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusConjLevelDetEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.DetIdeleUnit

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem val_eq_one_of_le {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 :=
  le_antisymm ha (by
    calc (1 : WithZero (Multiplicative ℤ)) = a * b := h.symm
      _ ≤ a := mul_le_of_le_one_right' hb)

theorem valued_isInt {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v}
    (h : GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) x) : Valued.v x ≤ 1 := by
  obtain ⟨o, rfl⟩ := h
  exact o.2

theorem chart_val_eq_one {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart es v π) {c c' : AE D} (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : Valued.v (π c) = 1 := by
  obtain ⟨φ, hφ, hint, -⟩ := GlobalTheory.ChartLevels.chart_levels D es PP v π he hπ
  have hc' : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c')) = 1 := by
    have h1 : GlobalTheory.StdFrames.cpt PP (toEAf D c) * GlobalTheory.StdFrames.cpt PP (toEAf D c') = 1 := by
      rw [← map_mul, ← map_mul, hcc, map_one, map_one]
    have h2 := congrArg Valued.v h1
    rw [map_mul, hc, one_mul, map_one] at h2
    exact h2
  have key : ∀ y : AE D, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D y)) = 1 → Valued.v (π y) ≤ 1 := by
    intro y hy
    rw [← hφ]
    refine valued_isInt ((hint _).1 ((GlobalTheory.AdIsom.mem_OA _).2 fun Q => ?_))
    rw [map_mul]
    by_cases hQ : Q = PP
    · subst hQ; rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul, hy]
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, map_zero]; exact zero_le'
  refine val_eq_one_of_le (key c hc) (key c' hc') ?_
  rw [← map_mul, ← map_mul, hcc, map_one, map_one]

theorem absFin_single {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) (u : (AE D)ˣ) (c : AE D)
    (hu : (u : AE D) = es * c + (1 - es)) (c' : AE D) (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D u = 1 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart es he.1
  have hee : es * es = es := he.1.1
  have hu1 : (1 - es) * (u : AE D) = 1 - es := by rw [hu]; linear_combination (1 - c) * hee
  rw [GlobalTheory.SplitLinear.absFin_split D es v π he.1 hπ u hu1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  have hπu : π (u : AE D) = π c := by
    rw [hu, map_add, map_mul, map_sub, map_one, hπ.map_e hee, one_mul, sub_self, add_zero]
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v (π (u : AE D)))) = 1
  rw [hπu, chart_val_eq_one he hπ hcc hc, WithZero.log_one, zpow_zero]

theorem absFin_idemSum_eq_one {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (x : (AE D)ˣ) (c c' : AE D)
    (hcc : c * c' = 1) (hx : (x : AE D) = e * c + (1 - e))
    (hc : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = 1 := by
  obtain ⟨⟨es, hes, hae⟩, -⟩ := he
  let u : {PP // PP ∈ P} → (AE D)ˣ := fun PP =>
    { val := es PP.1 * c + (1 - es PP.1)
      inv := es PP.1 * c' + (1 - es PP.1)
      val_inv := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 hcc
      inv_val := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }
  have hx' : x = ∏ PP ∈ P.attach, u PP := by
    apply Units.ext
    rw [hx, Units.coe_prod]
    change _ = ∏ PP ∈ P.attach, (fun PP => es PP * c + (1 - es PP)) PP.1
    rw [Finset.prod_attach P (fun PP => es PP * c + (1 - es PP)),
      GlobalTheory.SplitIdeleModulus.prod_idem hes _ P subset_rfl, hae]
  let A : (AE D)ˣ →* ℝ := ⟨⟨GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D, GlobalTheory.SplitIdeleModulus.absFin_one'⟩, GlobalTheory.SplitLinear.absFin_mul⟩
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = A x := rfl
  rw [hA, hx', map_prod]
  exact Finset.prod_eq_one fun PP _ => absFin_single (hes PP.1 PP.2) (u PP) c rfl c' hcc (hc PP.1 PP.2)

end GlobalTheory.DetIdeleUnit

open GlobalTheory.FunObj in
theorem GlobalTheory.DetIdeleUnit.cpt_gdet_kapAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
  ((gdet (GlobalTheory.TopLevelInv.kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) = GlobalTheory.StdFrames.cpt w ((finG (G.V (.top (j + 1))) k).val.det) := by
  have hu : IsUnit ((S.βp (j + 1)).val.det) := (Matrix.GeneralLinearGroup.det (S.βp (j + 1))).isUnit
  have ha : ((S.βp (j + 1)).val.map (GlobalTheory.StdFrames.cpt w)).det ≠ 0 := by
    intro h0; apply (hu.map (GlobalTheory.StdFrames.cpt w)).ne_zero; rw [RingHom.map_det]; exact h0
  unfold GlobalTheory.TopLevelInv.kapAt inBasis
  simp [gdet, GlobalTheory.StepData.reGL, Matrix.GeneralLinearGroup.det, GlobalTheory.StdFrames.loc, RingHom.map_det]
  rw [mul_right_comm, inv_mul_cancel₀ ha, one_mul]

theorem GlobalTheory.DetIdeleUnit.valued_eq_one_of_valuation {D : D7} {w : Pl D.host.E} (y : Kw w) (h : ValuativeRel.valuation (Kw w) y = 1) : Valued.v y = 1 := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  first
  | exact e.eq_one_iff_eq_one.1 h
  | exact le_antisymm (e.le_one_iff_le_one.1 h.le) (e.one_le_iff_one_le.1 h.ge)

namespace GlobalTheory.DetIdeleUnit

open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem det_mt_conj (V : HSp D) (h k : GA D V) :
    (Formalism.L2.Theta.mt V (h⁻¹ * k * h)).det = (Formalism.L2.Theta.mt V k).det := by
  rw [GlobalTheory.IdemSupport.mt_mul, GlobalTheory.IdemSupport.mt_mul, Matrix.det_mul, Matrix.det_mul,
    mul_comm (Formalism.L2.Theta.mt V h⁻¹).det, mul_assoc, ← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel,
    GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one, mul_one]

theorem cpt_det_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    (V : HSp D) (g : GA D V) :
    GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det) =
      GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det) := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc0 : e * cA D e = 0 := he.2
  obtain ⟨hf1, hf2⟩ := idem_conj_sum hee hc0
  obtain ⟨⟨es, hes, hae⟩, -⟩ := id he
  let ψ : AE D →+* Kw PP := (GlobalTheory.StdFrames.cpt PP).comp (toEAf D)
  have hψe : ψ e = 1 := by
    rw [hae, map_sum, Finset.sum_eq_single PP]
    · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · intro Q hQ hne
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).2 PP (Ne.symm hne)
    · intro h; exact absurd hPP h
  have hψc : ψ (cA D e) = 0 := by
    have := congrArg ψ hc0
    rwa [map_mul, hψe, one_mul, map_zero] at this
  have hψa : ψ (e + cA D e) = 1 := by rw [map_add, hψe, hψc, add_zero]
  show ψ _ = ψ _
  rw [RingHom.map_det, RingHom.map_det, mt_cutPart hf1 hf2]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, map_sub, map_one, hψa, one_mul, sub_self, zero_mul, add_zero]

theorem absFin_detAt_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hee : e * e = e) (V : HSp D)
    (g : GA D V) (hg : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det)) = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g)) = 1 :=
  absFin_idemSum_eq_one he _ (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det
    (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)⁻¹).det
    (by rw [← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]) rfl
    (fun PP hPP => by rw [cpt_det_cutPart he hPP]; exact hg PP hPP)

end GlobalTheory.DetIdeleUnit

open GlobalTheory.DetIdeleUnit in

theorem GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1 := by
  intro D T L sc G W U S t μ₀ hμ ht Φ β j hj k hk e he
  refine absFin_detAt_cutPart he _ _ _ fun PP hPP => ?_
  have h1 := GlobalTheory.TopLevelInv.valuation_gdet_kapAt S hj hk ⟨PP, hPP⟩
  rw [cpt_gdet_kapAt] at h1
  have h2 := valued_eq_one_of_valuation _ h1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, det_mt_conj]
  rw [RingHom.map_det]
  exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowInt

variable {D : D7}

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem smul_mem_latO_at : All fun {D} _ _ _ {G} _ _ =>
    ∀ i, i < D.R.m → ∀ v, ∀ e ∈ intAt D (· = v), ∀ u ∈ latRow G i,
      e • u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) := by
  intro D _ T L μ0 _ sc G W M _ i _ v e he u hu
  have h0 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := hu.1
  have h1 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := latO_negSp_le _ _ _ _ _ h0
  have h2 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e he.2 u h1
  have h3 : MxAt (· = v) (e • u) := fun a b => Ideal.mul_mem_right _ _ he.1
  exact (GlobalTheory.AscFinWit.mem_latO_at h3).1 h2

end GlobalTheory.RowInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.DepLat

variable {D : D7}

theorem finLat_of_nsmul {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : FinLat Λ) (hle : A ≤ Λ)
    {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a := continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

theorem finLat_depLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (p : Pair T), IsSelfDualC (G.pS p) (G.latS p) → IsSelfDualC (G.pT p) (G.latT p) → FinLat (depLat G p) := by
  intro D T L sc G p hS hT
  obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT p) (ΛT := G.latT p) hS (G.pl.modul_ne_bot sc)
  refine finLat_of_nsmul (GlobalTheory.AscFinWit.finLat_latO hS.1 hT.1) (fun u hu => hu.1) hK
    fun u hu => ⟨nsmul_mem hu K, fun e he => ?_⟩
  rw [smul_comm]
  exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])) _ hu)

end GlobalTheory.AscFin.DepLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelActionStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) := by
  first | exact @GlobalTheory.ShapeUVAny.shapeV_any | exact GlobalTheory.ShapeUVAny.shapeV_any | (intros; apply GlobalTheory.ShapeUVAny.shapeV_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelInvariantStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_invariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  first | exact @GlobalTheory.SchurCharV.exists_char_of_schur_any | exact GlobalTheory.SchurCharV.exists_char_of_schur_any | (intros; apply GlobalTheory.SchurCharV.exists_char_of_schur_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelMeasureStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_measure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  first | exact @GlobalTheory.MixedForm.char_eq_local_any | exact GlobalTheory.MixedForm.char_eq_local_any | (intros; apply GlobalTheory.MixedForm.char_eq_local_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelUnitaryStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) := by
  first | exact @GlobalTheory.UnitWShapeSplit.shape_split | exact GlobalTheory.UnitWShapeSplit.shape_split | (intros; apply GlobalTheory.UnitWShapeSplit.shape_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwiningStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_intertwining : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0) →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  first | exact @GlobalTheory.HoweGlobal.allInKer | exact GlobalTheory.HoweGlobal.allInKer | (intros; apply GlobalTheory.HoweGlobal.allInKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedFiniteDatumEqHeisenbergCombinationVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (d : FinDatum ch.G t p) (c : WO (ch.G.pS p) (ch.G.pT p) →₀ ℂ), d.z = 1 → ch.S.Z.HasVec d → IsCombOf ch.W d c → movedVec t ch.S.toGridChoice d = comb ch.W.ψ _ _ c (ch.W.om p (ch.G.toPair p (ch.S.N.u p.small).1 (ch.S.N.u p.big).1) (ch.S.Z.vac p)) := by
  first | exact @GlobalTheory.MovedComb.movedVec_eq_comb | exact GlobalTheory.MovedComb.movedVec_eq_comb | (intros; apply GlobalTheory.MovedComb.movedVec_eq_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelWeilDoublingAssemblyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_doubling_assembly : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.PrimIn.Hypotheses3 := by
  first | exact @GlobalTheory.PrimIn.hypotheses3_intro | exact GlobalTheory.PrimIn.hypotheses3_intro | (intros; apply GlobalTheory.PrimIn.hypotheses3_intro <;> assumption)
end

