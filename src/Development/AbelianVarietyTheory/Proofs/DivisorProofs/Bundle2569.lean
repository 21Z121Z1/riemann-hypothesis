import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def transl {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : G ⟶ G :=
  𝟙 G * (Over.homMk G.hom (by simp) ≫ y)

def Near.chart {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) : Option (Fin n) → (pullback N.U.hom π ⟶ G.left)
  | none => N.u
  | some k => N.u ≫ (transl (x k)⁻¹).left

@[simp] theorem Near.chart_none {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    [GrpObj G] (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) : N.chart x none = N.u := rfl

theorem Near.chart_some {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    [GrpObj G] (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) (k : Fin n) :
    N.chart x (some k) = N.u ≫ (transl (x k)⁻¹).left := rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.ChartGlue GlobalTheory.Points
open Topology Filter

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem cHess_zero (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

variable {A B : LB X} {c : AlgChart p σ D} {y : CxPts p σ}

theorem hess_tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf) (hy : y ∈ c.e.source)
    {a : A.ι} {b : B.ι} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (ψ.tens φ) (a, b) y = c.hess ψ a y + c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (hψ a) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    ((contDiffOn_chart (hφ b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
  simp only [one_mul, Complex.ofReal_one, one_smul] at e
  exact e

theorem hess_dual {φ : Weight p σ B} (hφ : φ.IsCInf) (hy : y ∈ c.e.source) {b : B.ι}
    (hb : y ∈ ptsIn p σ (B.U b)) : c.hess φ.dual b y = -c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U b))
  have hm := mem_over c.e hy hb
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ b) c) (-1) hm
  rw [cHess_zero, zero_add] at e
  simp only [zero_add, neg_one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul] at e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.dual.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y) =
    -ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y)
  refine (congrArg (fun g => ReciprocityTheory.L2DbarEstimates.cHess D g (c.e y)) ?_).trans e
  funext v
  simp only [Function.comp_apply]
  exact Complex.ofReal_neg _

theorem hess_zpow {φ : Weight p σ B} (hφ : φ.IsCInf) (hy : y ∈ c.e.source) (n : ℤ) (j : PUnit → B.ι)
    (hb : y ∈ ptsIn p σ (B.U (j PUnit.unit))) : c.hess (φ.zpow n) j y = (n : ℂ) • c.hess φ (j PUnit.unit) y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (j PUnit.unit)))
  have hm := mem_over c.e hy hb
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ (j PUnit.unit)) c) n hm
  rw [cHess_zero, zero_add] at e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((φ.zpow n).φ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) =
    (n : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.φ (j PUnit.unit) (c.e.symm v) : ℝ) : ℂ)) (c.e y)
  rw [show ((n : ℂ)) = (((n : ℝ) : ℂ)) by push_cast; rfl]
  refine (congrArg (fun g => ReciprocityTheory.L2DbarEstimates.cHess D g (c.e y)) ?_).trans e
  funext v
  simp only [Function.comp_apply, Weight.zpow_φ, zero_add]

def HessFlat (φ : Weight p σ B) (D : ℕ) : Prop :=
  ∀ (c : AlgChart p σ D) (y : CxPts p σ) (i : B.ι), y ∈ c.e.source → y ∈ ptsIn p σ (B.U i) → c.hess φ i y = 0

theorem hessFlat_zp {M : HermLB p} (h : HessFlat (M.φ σ) D) (m : ℤ) : HessFlat ((zp M m).φ σ) D := by
  intro c y i hy hi
  obtain ⟨hi₁, hi₂⟩ := mem_ptsIn_inf.1 hi
  have h₁ : y ∈ ptsIn p σ (M.B.U (i.1 PUnit.unit)) := (mem_pow_iff (n := ((m.toNat : ℕ) : ℤ)) (j := i.1)).1 hi₁
  have h₂ : y ∈ ptsIn p σ (M.B.U (i.2 PUnit.unit)) := (mem_pow_iff (n := (((-m).toNat : ℕ) : ℤ)) (j := i.2)).1 hi₂
  have e := hess_tens ((M.cInf σ).zpow _) ((M.cInf σ).zpow _).dual hy hi₁ hi₂
  change c.hess (((M.φ σ).pow m.toNat).tens ((M.φ σ).pow (-m).toNat).dual) (i.1, i.2) y = 0
  rw [e, hess_dual ((M.cInf σ).zpow _) hy hi₂, hess_zpow (M.cInf σ) hy _ _ h₁,
    hess_zpow (M.cInf σ) hy _ _ h₂, h c y _ hy h₁, h c y _ hy h₂]
  simp

theorem chernDens_tens_flat {L N : HermLB p} (h : HessFlat (N.φ σ) D) (hy : y ∈ c.e.source) :
    c.chernDens ((L.tens N).φ σ) y = c.chernDens (L.φ σ) y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (N.φ σ).isLB y
  rw [c.chernDens_eq ((L.tens N).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (N.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩), c.chernDens_eq (L.cInf σ) hy ha]
  change _ * (c.hess ((L.φ σ).tens (N.φ σ)) _ y).det.re = _
  rw [hess_tens (L.cInf σ) (N.cInf σ) hy ha hb, h c y _ hy hb, add_zero]

theorem chernPart_tens_flat {L N : HermLB p} (h : HessFlat (N.φ σ) D) (ε : ℤˣ) :
    ((L.tens N).φ σ).chernPart D ε = (L.φ σ).chernPart D ε := by
  refine iSup_congr fun c => congrArg (MeasureTheory.Measure.map _) (MeasureTheory.withDensity_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_))
  simp only [Function.comp_apply, chernDens_tens_flat h (c.e.map_target hv)]

theorem isometric_comb_update {ι : Type} [Fintype ι] [DecidableEq ι] (L : ι → HermLB p) (n : ι → ℤ) (i : ι) :
    (comb L n).Isometric ((comb L (Function.update n i 0)).tens (zp (L i) (n i))) := by
  refine HermLB.icls_eq_iff.1 ?_
  rw [HermLB.icls_tens, icls_comb, icls_comb, icls_zp]
  have key : ∀ j, n j • (L j).icls = Function.update n i 0 j • (L j).icls + (Pi.single i (n i) : ι → ℤ) j • (L j).icls := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib]
  congr 1
  simp [Pi.single_apply]

end GlobalTheory.FlatMass

namespace GlobalTheory.FlatMass

open GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem hessFlat_of_norms (V : Cover Y) (M : HermLB V.p)
    {lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ}
    (hN : Norms V M (fun _ => 1) (fun _ _ => 0) lg) (σ : 𝓞 F →+* ℂ) (D : ℕ) : HessFlat (M.φ σ) D := by
  have hinj : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))
  obtain ⟨τ, rfl⟩ : ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = σ :=
    ⟨IsFractionRing.lift (K := F) hinj, RingHom.ext fun x => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  intro c y₀ a hy₀ ha
  have hsp (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) :
      z.1 ≫ V.p = spMap τ ≫ spMap (algebraMap (𝓞 F) F) :=
    z.2.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))
  let lift (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) : CxPts (V.π ≫ Y.str) τ :=
    ⟨V.pb.lift z.1 (spMap τ) (hsp z), V.pb.lift_snd _ _ _⟩
  have hj (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) : (lift z).1 ≫ V.j = z.1 := V.pb.lift_fst _ _ _
  have hunder (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) : V.j (under (lift z)) = under z := by
    show V.j ((lift z).1 _) = z.1 _
    rw [← hj z]
    rfl
  obtain ⟨r, -, hu, hc, -⟩ := hN
  let ja : (M.B.pull V.j).ι := fun _ => a
  have hmem (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (M.B.U a)) :
      under (lift z) ∈ (M.B.pull V.j).U ja :=
    mem_pull.2 (by rw [hunder]; exact mem_ptsIn.1 hz)
  have hunit (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (M.B.U a)) :
      UnitAt (under (lift z)) (r ja : V.G.functionField) := by
    simpa using hu ja _ (hmem z hz)
  obtain ⟨U, hxU, g, hg⟩ := (hunit y₀ ha).regAt.exists_fnOf
  obtain ⟨W', hW, hxW, n, g', hn, hg'⟩ :=
    T.exists_integral_multiple_extension F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb U _ hxU Unit (fun _ => g)
  have hpre (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ W') :
      lift z ∈ ptsIn (V.π ≫ Y.str) τ (V.j ⁻¹ᵁ W') := by
    refine mem_ptsIn.2 ?_
    show V.j (under (lift z)) ∈ W'
    rw [hunder]
    exact mem_ptsIn.1 hz
  have hval (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ W') :
      (n : ℂ) * ratVal (r ja : V.G.functionField) (lift z) = ev V.p _ W' (g' ()) z := by
    have h1 := hpre z hz
    rw [← hg, ratVal_fnOf (mem_ptsIn.2 (hW (mem_ptsIn.1 h1))), ← ev_res hW h1 g]
    show (n : ℂ) * valR (lift z).1 (V.j ⁻¹ᵁ W') (resG V.G hW g) = valR z.1 W' (g' ())
    rw [← hj z, ← Cover.valR_app_comp (lift z).1 V.j W' h1, ← hg' (), ZH.CrdCalc.valR_eq _ _ h1,
      ZH.CrdCalc.valR_eq _ _ h1, map_mul, map_natCast]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hweight (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (W' ⊓ M.B.U a)) :
      (M.φ _).φ a z = Real.log (‖(n : ℂ)⁻¹ * ev V.p _ W' (g' ()) z‖ ^ 2) := by
    obtain ⟨hz₁, hz₂⟩ := mem_ptsIn_inf.1 hz
    have H := hc τ (lift z) ⟨(lift z).1 ≫ V.π, by rw [Category.assoc]; exact (lift z).2⟩ z ja rfl (hj z).symm
      (hmem z hz₂)
    rw [← hval z hz₁, ← mul_assoc, inv_mul_cancel₀ hn', one_mul, Real.log_pow]
    simp only [map_one, one_mul] at H
    change (0 : ℝ) = _ - (M.φ _).φ a z / 2 at H
    push_cast
    linarith
  have hne (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (W' ⊓ M.B.U a)) :
      (n : ℂ)⁻¹ * ev V.p _ W' (g' ()) z ≠ 0 := by
    obtain ⟨hz₁, hz₂⟩ := mem_ptsIn_inf.1 hz
    rw [← hval z hz₁, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
    exact ratVal_ne_zero (hunit z hz₂)
  have hy₀W : y₀ ∈ ptsIn V.p _ W' := by
    refine mem_ptsIn.2 ?_
    show under y₀ ∈ W'
    rw [← hunder y₀]
    exact hxW
  have ho := isOpen_over c.e (isOpen_ptsIn (p := V.p) (σ := τ.comp (algebraMap (𝓞 F) F)) (W' ⊓ M.B.U a))
  have hm := mem_over c.e hy₀ (mem_ptsIn_inf.2 ⟨hy₀W, ha⟩)
  have hol : DifferentiableOn ℂ (fun v => (n : ℂ)⁻¹ * ev V.p _ W' (g' ()) (c.e.symm v))
      (c.e.target ∩ c.e.symm ⁻¹' ptsIn V.p _ (W' ⊓ M.B.U a)) :=
    ((c.holo W' (g' ())).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩).const_mul _
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((M.φ _).φ a (c.e.symm v) : ℝ) : ℂ)) (c.e y₀) = 0
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr (g₂ := fun v =>
    ((Real.log (‖(n : ℂ)⁻¹ * ev V.p _ W' (g' ()) (c.e.symm v)‖ ^ 2) : ℝ) : ℂ)) ?_]
  · ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hol (fun v hv => hne _ hv.2) i j
  · filter_upwards [ho.mem_nhds hm] with v hv
    rw [hweight _ hv.2]

theorem chernInt_comb_update_of_norms : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (D : ℕ), Y.dim = D → ∀ (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : ι → HermLB V.p) (i : ι), L i = M → ∀ (n : ι → ℤ) (σ : 𝓞 F →+* ℂ), ((comb L n).φ σ).chernInt D Set.univ (fun _ => 1) = ((comb L (Function.update n i 0)).φ σ).chernInt D Set.univ (fun _ => 1) := by
  intro _ F _ _ Y V D _ M lg hN ι _ _ L i hLi n σ
  subst hLi
  have hflat : HessFlat ((zp (L i) (n i)).φ σ) D := hessFlat_zp (hessFlat_of_norms V (L i) hN σ D) (n i)
  rw [(isometric_comb_update L n i).chernInt_eq σ D]
  simp only [Weight.chernInt, chernPart_tens_flat hflat]

end GlobalTheory.FlatMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiEqOfTorsion
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (x : T ⟶ A) (m : ℕ) : ρ ≫ x ^ m = (ρ ≫ x) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem chi_eq_of_torsion : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    (n : R) = 0 → HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ g : Fn2 A, IsSecAdd n S g →
    ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb S hS g hg D _ _ x hx
  obtain ⟨E, _, _, ψ, z, hff, hz⟩ := hR D x
  apply hff.injective
  change ψ (chi n g D x) = ψ (b D x)
  have hpow : ∀ i : ℕ, (z ^ i) ^ n = spOver ψ ≫ x ^ i := by
    intro i
    rw [← pow_mul, mul_comm, pow_mul, hz, comp_pow_pt]

  have hterm : ∀ i : ℕ, ψ (g D (x ^ i) x) =
      (S D (x ^ (i + 1)) E ψ (z ^ (i + 1)) - S D (x ^ i) E ψ (z ^ i)) - S D x E ψ z := by
    intro i
    have h := hg D (x ^ i) x E ψ (z ^ i) z (hpow i) hz
    rw [← pow_succ, ← pow_succ] at h
    rw [h]
  have hnE : (n : E) = 0 := by
    rw [← map_natCast (algebraMap R E), hn, map_zero]
  have hsum : ψ (chi n g D x) = S D (x ^ n) E ψ (z ^ n) - S D (x ^ 0) E ψ (z ^ 0) := by
    simp only [chi, map_sum, hterm, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ S D (x ^ i) E ψ (z ^ i)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnE, zero_mul, sub_zero]
  rw [hsum, hx, pow_zero, pow_zero]

  have h1 : (1 : Pt A E) ^ n = spOver ψ ≫ (1 : Pt A D) := by rw [one_pow, MonObj.comp_one]
  have h2 : (z ^ n) ^ n = 1 := by rw [hz, ← comp_pow_pt, hx, MonObj.comp_one]
  have hs := (hS D 1).2 E ψ 1 (z ^ n) h1 h2
  rw [_root_.one_mul] at hs
  rw [hs, add_sub_cancel_left, hz]
  exact hb.1 D E ψ x hx

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classifyingMap_symplecticLevel_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  first | exact @GlobalTheory.HTSympCover.classify_equivariant | exact GlobalTheory.HTSympCover.classify_equivariant | (intros; apply GlobalTheory.HTSympCover.classify_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingLiftSeparatedFiniteTypeQuasi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem emb_lift_sep_loft_qc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G',
    IsSeparated (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      LocallyOfFiniteType (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      QuasiCompact (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) := by
  intro R _ _ _ hR M G' _ _ hG E
  have : IsNoetherianRing R := hR.1
  have : Smooth G'.hom := hG.smooth
  have : IsSeparated G'.hom := hG.separated
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : IsProper M.π := M.proper
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : IsProper (PSpace.str R E.N) := isProper_str R E.N
  set φ := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over
  have hφ : φ ≫ pullback.snd (PSpace.str R E.N) M.π = E.H.ι ≫ G'.hom := pullback.lift_snd _ _ _
  have h1 : IsSeparated (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h2 : LocallyOfFiniteType (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h3 : QuasiCompact (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  exact ⟨IsSeparated.of_comp φ (pullback.snd _ _), locallyOfFiniteType_of_comp φ (pullback.snd _ _),
    QuasiCompact.of_comp φ (pullback.snd _ _)⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingMulImageEqOfFieldPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem closed_product_image (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G']
    (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme)
    (hl : l ≫ E.H.ι = N.u) (hf : l ≫ E.f = pullback.fst _ _ ≫ fU) (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω)
    (s : Sp Ω ⟶ M.S) (a b c : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (hs : s ≫ M.π = spMap (κ.comp (residue R)))
    (ha : N.Pt s a x.left) (hb : N.Pt s b y.left) (hc : N.Pt s c (x * y).left) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (ca cb : Over.mk (spMap (io.comp κ)) ⟶ E.Y),
      ca.left ≫ E.j = spMap io ≫ a ≫ fU ∧ cb.left ≫ E.j = spMap io ≫ b ≫ fU ∧
      (ca * cb).left ≫ E.j = spMap io ≫ c ≫ fU := by
  obtain ⟨Ω', _, io, e, l', he, hl1, hl2⟩ := E.fib Ω s κ hs
  haveI : IsMonHom e.hom := he
  have hP := isGrpPullback_pullback G' (spMap io ≫ s)
  have hY : IsGrpPullback ((Over.pullback (spMap io ≫ s)).obj G') E.Y (spMap (io.comp κ)) (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback E.Y (spMap (io.comp κ)))).congr (Category.id_comp _) rfl

  let sec : (Over.mk s ⟶ G') → (Over.mk (𝟙 (Sp Ω')) ⟶ (Over.pullback (spMap io ≫ s)).obj G') := fun z =>
    Over.homMk (pullback.lift (spMap io ≫ z.left) (𝟙 _) (by
      rw [Category.assoc, Over.w z, Category.id_comp]; rfl)) (pullback.lift_snd _ _ _)
  have sec_fst : ∀ z, (sec z).left ≫ pullback.fst G'.hom (spMap io ≫ s) = spMap io ≫ z.left := fun z => pullback.lift_fst _ _ _

  have sec_mul : sec (x * y) = sec x * sec y := by
    let r : Over.mk (𝟙 (Sp Ω') ≫ (spMap io ≫ s)) ⟶ Over.mk s := Over.homMk (spMap io) (by simp)
    have e₁ := hP.2 (Over.mk (𝟙 (Sp Ω'))) (sec x) (sec y) (r ≫ x) (r ≫ y) (sec_fst x).symm (sec_fst y).symm
    rw [← MonObj.comp_mul] at e₁
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [sec_fst, ← e₁]; rfl
    · have h1 := Over.w (sec (x * y))
      have h2 := Over.w (sec x * sec y)
      simp only [Over.mk_hom] at h1 h2
      exact h1.trans h2.symm

  let cp : (Over.mk s ⟶ G') → (Over.mk (spMap (io.comp κ)) ⟶ E.Y) := fun z =>
    Over.homMk ((sec z).left ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) (by
      have h := Over.w (pushPt hY.1.w (sec z))
      simp only [Over.mk_hom, pushPt, Over.homMk_left] at h
      simpa using h)
  have cp_mul : (cp x * cp y).left = (cp (x * y)).left := by
    have e₂ := hY.2 (Over.mk (𝟙 (Sp Ω'))) (sec x) (sec y) (pushPt hY.1.w (sec x)) (pushPt hY.1.w (sec y)) rfl rfl
    rw [← sec_mul] at e₂
    refine Eq.trans ?_ e₂
    exact mul_left_congr (Category.id_comp (spMap (io.comp κ))).symm _ _ _ _ rfl rfl

  have img : ∀ (z : Over.mk s ⟶ G') (d : Sp Ω ⟶ N.U.left), N.Pt s d z.left → (cp z).left ≫ E.j = spMap io ≫ d ≫ fU := by
    intro z d ⟨z₀, h₁, _, h₃⟩
    have hsec : (sec z).left ≫ l' = spMap io ≫ z₀ ≫ l := by
      rw [← cancel_mono E.H.ι, Category.assoc, hl1, sec_fst, Category.assoc, Category.assoc, hl, h₃]
    show ((sec z).left ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = _
    rw [Category.assoc, Category.assoc, ← hl2, ← Category.assoc, hsec, Category.assoc, Category.assoc, hf,
      ← Category.assoc z₀, h₁]
  exact ⟨Ω', inferInstance, io, cp x, cp y, img x a ha, img y b hb, by rw [cp_mul]; exact img _ c hc⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibrePullH1Abelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_of_iso {k : Type} [CommRing k] {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k) (e : X' ≅ X)
    (he : e.hom ≫ s = s') (hW : WedgeO (OAff s)) : WedgeO (OAff s') := by
  have h1 : e.hom ≫ s = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, he]
  have h2 : e.inv ≫ s' = s ≫ spMap (RingHom.id k) := by
    rw [spMap_id, Category.comp_id, ← he, Iso.inv_hom_id_assoc]
  have hid : (𝟙 X) ≫ s = s ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have hid' : (𝟙 X') ≫ s' = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have P := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  have c1 := (P.1 k k X X' s s' (RingHom.id k) e.hom h1 k X s (RingHom.id k) e.inv h2 (RingHom.id k) (𝟙 X) hid
    (by simp) (fun _ ↦ rfl))
  have c2 := (P.1 k k X' X s' s (RingHom.id k) e.inv h2 k X' s' (RingHom.id k) e.hom h1 (RingHom.id k) (𝟙 X') hid'
    (by simp) (fun _ ↦ rfl))
  have i1 := P.2.2 k (Over.mk s)
  have i2 := P.2.2 k (Over.mk s')
  have hcup := (P.2.1 k k X X' s s' (RingHom.id k) e.hom h1).1

  let f1 : HO1 s →ₗ[k] HO1 s' := pullHO1 h1
  let g1 : HO1 s' →ₗ[k] HO1 s := pullHO1 h2
  let f2 : HO2 s →ₗ[k] HO2 s' := pullHO2 h1
  let g2 : HO2 s' →ₗ[k] HO2 s := pullHO2 h2
  have fg1 : ∀ a, f1 (g1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c2.1]; exact i2.1 a
  have gf1 : ∀ a, g1 (f1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c1.1]; exact i1.1 a
  have fg2 : ∀ a, f2 (g2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c2.2.1]; exact i2.2.1 a
  have gf2 : ∀ a, g2 (f2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c1.2.1]; exact i1.2.1 a
  let e2 : HO2 s ≃ₗ[k] HO2 s' := LinearEquiv.ofLinear f2 g2 (LinearMap.ext fg2) (LinearMap.ext gf2)
  let eΛ : ⋀[k]^2 (HO1 s') ≃ₗ[k] ⋀[k]^2 (HO1 s) :=
    LinearEquiv.ofLinear (exteriorPower.map 2 g1) (exteriorPower.map 2 f1)
      (by rw [← exteriorPower.map_comp, show g1 ∘ₗ f1 = LinearMap.id from LinearMap.ext gf1,
        exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, show f1 ∘ₗ g1 = LinearMap.id from LinearMap.ext fg1,
        exteriorPower.map_id])
  obtain ⟨E, hE⟩ := hW
  refine ⟨(eΛ.trans E).trans e2, fun a b ↦ ?_⟩
  have hm : (⇑g1 ∘ ![a, b]) = ![g1 a, g1 b] := by
    ext i; fin_cases i <;> rfl
  change f2 (E (exteriorPower.map 2 g1 (exteriorPower.ιMulti k 2 ![a, b]))) = _
  rw [exteriorPower.map_apply_ιMulti, hm, hE]
  simp only [f2]
  rw [hcup]
  rw [show pullHO1 h1 (g1 a) = a from fg1 a, show pullHO1 h1 (g1 b) = b from fg1 b]

end GlobalTheory.AbCohWedgeLift

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_fibre : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  intro hF R _ A _ g hA hg k _ σ X₀ s₀ ψ w
  letI : Algebra R k := σ.toAlgebra
  obtain ⟨B, _, pr, -, hB, hBg, hsq, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R k A g hA hg
  have hsq' : IsPullback pr B.hom A.hom (spMap σ) := hsq
  have hW : WedgeO (OAff B.hom) := (hF k (Field.toIsField k) B g hB hBg).2.2
  let e : X₀ ≅ B.left := IsPullback.isoIsPullback _ _ w hsq'
  exact wedgeO_of_iso B.hom s₀ e (IsPullback.isoIsPullback_hom_snd _ _ w hsq') hW

end GlobalTheory.AbCohWedgeLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDualIntegralImageStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_dual_integral_image : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ), ρ ≠ 0 →
    Submodule.span ℝ (Φ '' L) = ⊤ →
    (∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q) →
    ∀ w : Fin n → ℂ, (∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) → ∃ x : E, w = Φ x := by
  first | exact @GlobalTheory.CxDescent.mem_range_of_int_pairing | exact GlobalTheory.CxDescent.mem_range_of_int_pairing | (intros; apply GlobalTheory.CxDescent.mem_range_of_int_pairing <;> assumption)
end

