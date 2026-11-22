import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0622
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0724
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ExponentSeparationLemma.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import GroundTheory.AutomorphicForms.Satake
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0722
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0065
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0716
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0725
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetClosedOpenSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemExTrans
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RgTrans

private theorem mul_mul_mul_smul_eq_smul_mul_mul_mul {A : Type*} [CommRing A] {a b c d f : Type*} [Fintype b] [Fintype c]
    [Fintype d] (R : Matrix a b A) (P : Matrix b c A) (G : Matrix c d A) (X : Matrix d f A) (e : A) :
    R * (P * (G * (e • X))) = e • (R * (P * (G * X))) := by
  simp only [Matrix.mul_smul]

private theorem yv_smul_snd {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (e : AE D)
    (w : Mx D V.rank r × Mx D V.rank t) :
    yv V b₀ (w.1, e • w.2) = e • yv V b₀ w :=
  mul_mul_mul_smul_eq_smul_mul_mul_mul _ _ _ _ e

theorem idemEx_trans : IdemEx → Trans := by
  intro hI D r t V b₀ hb₀ S e he
  have hee : e * e = e := ((hI D S).2 e he).1
  have hce : cA D e = e := ((hI D S).2 e he).2
  refine ⟨GlobalTheory.CompanionTheory.FreeFrames.isOpen_free D r t V.rank e hee
    (GlobalTheory.CompanionTheory.UnitNbhd.exists_open_mul_eq_idem GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D S e he), ?_⟩
  intro z z' hz hz' hzc hz'c
  obtain ⟨Γ, hΓ, hN⟩ := GlobalTheory.CompanionTheory.FrameComplete.frame_completes D r t V b₀ hb₀ e hee hce
  obtain ⟨N, hNe, hNg, hN1, hN2⟩ := hN z hz hzc
  obtain ⟨N', hN'e, hN'g, hN'1, hN'2⟩ := hN z' hz' hz'c
  obtain ⟨h, hh, hhN⟩ := GlobalTheory.CompanionTheory.WittS.exists_unitary_off_S
    (GlobalTheory.CompanionTheory.SPartTensor.sPart GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps) D V S e he _ Γ hΓ N N'
    hNe hN'e hNg hN'g
  have hy : ∀ w : Mx D V.rank r × Mx D V.rank t, e • w.2 = w.2 → e • yv V b₀ w = yv V b₀ w := by
    intro w hw
    have key : yv V b₀ w = e • yv V b₀ w := by
      calc yv V b₀ w = yv V b₀ (w.1, e • w.2) := by rw [hw]
        _ = e • yv V b₀ w := yv_smul_snd V b₀ e w
    rw [key, smul_smul, hee]
  have h1 : mm (mt V h) z.1 = z'.1 := by
    ext i j
    rw [← hN'1, ← hhN]
    simp only [mm, Matrix.mul_apply, hN1]
  have h2 : mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) = z'.2 - mm z'.1 (yv V b₀ z') := by
    ext i j
    rw [← hN'2, ← hhN]
    simp only [mm, Matrix.mul_apply, hN2]
  refine ⟨h, yv V b₀ z' - yv V b₀ z, hh, ?_, ?_⟩
  · rw [smul_sub, hy z' hz'c.2.1, hy z hzc.2.1]
  · have h3 : mm (mt V h) (z.2 + mm z.1 (yv V b₀ z' - yv V b₀ z)) =
        mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) + mm (mm (mt V h) z.1) (yv V b₀ z') := by
      simp only [mm, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
      abel
    refine Prod.ext h1.symm ?_
    rw [h3, h1, h2]
    simp only [mm, sub_add_cancel]

end GlobalTheory.CompanionTheory.RgTrans
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_principalSeriesSpace_of_indSp {n : ℕ} (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n))
      ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)) :
    (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) :=
  GlobalTheory.T.induced_in_principal_series k n α f

theorem isSatakeParameter_of_isSubquotient_of_injective {n : ℕ} (α : Fin n → ℂˣ) {X V : Type}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) k) X}
    (hρ : IsSmooth ρ) (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))) (hι : Function.Injective ι)
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π ρ)
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  GlobalTheory.T.subquotient_principal_series_bound k n α X V ρ hρ ι hι π h μ

theorem KO_eq_integralGL (n : ℕ) : KO k (Fin n) = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) : fixed ρ H = GroundTheory.Automorphic.fixedVectors ρ H := by
  ext v
  simp [fixed, eig, GroundTheory.Automorphic.fixedVectors]

def bridge {n : ℕ} (α : Fin n → ℂˣ) :
    (prinSeries fun i => unrChar k (α i)).IntertwiningMap (principalSeries k n (paramChar k α)) where
  toFun f := ⟨fun g => f.1.1 g, mem_principalSeriesSpace_of_indSp α f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' g := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl)

theorem bridge_injective {n : ℕ} (α : Fin n → ℂˣ) : Function.Injective (bridge (k := k) α) := fun f f' e =>
  by
  have := congrArg Subtype.val e
  apply Subtype.ext
  apply Subtype.ext
  exact this

theorem isSatakeParameter_of_isSubquotient {n : ℕ} (α : Fin n → ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π (prinSeries fun i => unrChar k (α i)))
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  isSatakeParameter_of_isSubquotient_of_injective α (isSmooth_parInd _ _) (bridge α) (bridge_injective α) h μ

theorem hasSupport_prinSeries (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (π : IrrRep (GL (Fin n) k)) (h : IsSubquotient π.ρ (prinSeries χ)) :
    HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  have H : GlobalTheory.SmGL.IsCuspSupport π.ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨π.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.CompanionTheory.SphSupp

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSpherical_iff_fixedVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) :
    IsSpherical π ↔ GroundTheory.Automorphic.fixedVectors π (GroundTheory.Automorphic.GLnLocal.integralGL k n) ≠ ⊥ := by
  show fixed π (KO k (Fin n)) ≠ ⊥ ↔ _
  rw [KO_eq_integralGL, fixed_eq_fixedVectors]

end GlobalTheory.CompanionTheory.SphSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsPermCell {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) : Prop :=
  ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0

def permMatrix {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (e : Fin c ≃ Fin l)
    (h : ∀ a, y a = x (e a)) : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) :=
  ⟨fun i j => if e j = i then (x i).1 else 0, fun i => by
    rw [Finset.sum_eq_single (e.symm i) (fun j _ hj => if_neg fun h' => hj (by rw [← h', e.symm_apply_apply]))
      (by simp)]
    simp, fun j => by
    rw [Finset.sum_ite_eq]
    simp [h j]⟩

set_option maxHeartbeats 2000000 in

theorem exists_choice (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) :
    ∃ (f : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      ∀ b, IsPermCell x y b →
        jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) = 1 := by
  classical
  have key : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), IsPermCell x y b → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    rintro b ⟨e, he, hb⟩
    exact GlobalTheory.T.size_matrix_permutation_equivs_exist hA x y e he b hb
  have key' : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      IsPermCell x y b → jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    intro b
    by_cases h : IsPermCell x y b
    · obtain ⟨f, g, hfg⟩ := key b h
      exact ⟨f, g, fun _ => hfg⟩
    · exact ⟨b.nonempty_rows.some, b.nonempty_cols.some, fun h' => absurd h' h⟩
  choose f g hfg using key'
  exact ⟨f, g, hfg⟩

theorem card_permCell {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (hxc : ∀ a, (x a).IsCusp)
    [Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))] [DecidablePred (IsPermCell x y)] :
    (Finset.univ.filter (IsPermCell x y)).card = Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun e he => permMatrix x y e (Set.mem_toFinset.1 he)) ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, Set.mem_toFinset.1 he, fun i j => rfl⟩
  · intro e he e' he' H
    refine Equiv.ext fun j => ?_
    have h2 := congrArg (fun b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) => b.1 (e j) j) H
    simp only [permMatrix, if_true] at h2
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h2
    exact (hxc (e j)).1.ne' h2
  · intro b hb
    obtain ⟨e, he, hb⟩ := (Finset.mem_filter.1 hb).2
    exact ⟨e, Set.mem_toFinset.2 he, Subtype.ext (funext fun i => funext fun j => (hb i j).symm)⟩

set_option maxHeartbeats 1000000 in

theorem main (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c N : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k)
    (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp) :
    jm y hy (prodIrr x hx) = (Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} : ℕ∞) := by
  classical
  haveI : Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) := Fintype.ofFinite _
  obtain ⟨f, g, hfg⟩ := exists_choice hA x y
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (y j).2.rep
  have h1 := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1.jhMult_eq (stdBlocks (fun a => (x a).1) hx)
    (stdBlocks (fun a => (y a).1) hy) (isSmooth_piTensor fun i => (x i).2.rep.smooth) f g hτ
  have hterm : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) =
      if IsPermCell x y b then 1 else 0 := by
    intro b
    split_ifs with h
    · exact hfg b h
    · by_contra hne
      exact h (GlobalTheory.T.cuspidal_cell_multiplicity_of_size_matrix x y hxc hyc b (f b) (g b) hne)
  have h2 : jm y hy (prodIrr x hx) = jhMult (piTensor fun j => (y j).rep)
      (jac (stdBlocks (fun a => (y a).1) hy) (parInd (stdBlocks (fun a => (x a).1) hx)
        (piTensor fun i => (x i).rep))) := rfl
  rw [h2, h1, Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_boole, card_permCell x y hxc]

end GlobalTheory.CompanionTheory.CuspJm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerVolumeAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab

section Rows

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_latV_iff_rows {d M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ a, (fun _ : Fin 1 => X a) ∈ latV b v :=
  ⟨fun h a _ i k => h a i k, fun h a i k => h a 0 i k⟩

theorem actW_mem_iff (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J)
    (hg : latStab σ J b v g) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    actW (Fv F v) σ J g X ∈ latV b v ↔ X ∈ latV b v := by
  rw [mem_latV_iff_rows, mem_latV_iff_rows b v X]
  exact forall_congr' fun a => hg fun _ => X a

theorem consA_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (a : Fin 1 → Fin n → Fv F v ⊗[F] E) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    consA a Y ∈ latV b v ↔ a ∈ latV b v ∧ Y ∈ latV b v := by
  constructor
  · intro hX
    refine ⟨fun p j k => ?_, fun j i k => ?_⟩
    · have := hX j.succ 0 k
      rw [Subsingleton.elim p 0]
      simpa [consA] using this
    · have := hX j.succ i.succ.succ k
      simpa [consA] using this
  · rintro ⟨ha, hY⟩ p
    refine Fin.cases ?_ (fun j => ?_) p
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consA] using GlobalTheory.CompanionTheory.SW.LatRat.one_mem_latR h k
      · simp [consA]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consA] using ha 0 j k
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [consA]
        · intro k
          simpa [consA] using hY j i k

end Rows

theorem stageInt_latStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ (m : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)), latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam m ((latV b v).indicator 1) g = m (latV b v) := by
  intro F E _ _ _ _ _ σ hCM M J _ n d b
  have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
      algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => GlobalTheory.CompanionTheory.SW.LatRat.eventually_integral (b.repr (1 : E) k)
  filter_upwards [h0] with v hv
  intro lam hlam m g hg
  classical
  have hmass : coordW (Fv F v) b lam 1 n (latV b v) = 1 := by
    choose std hstd using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
    have hfam : ∀ w, IsStdV w (Function.update std v lam w) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa using hlam
      · simpa [Function.update_of_ne hw] using hstd w
    simpa using GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hCM b (Function.update std v lam) hfam 1 n v
  have hin : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E,
      ∫⁻ a, (latV b v).indicator 1 (actW (Fv F v) σ (hypOne J) g (consA a Y))
        ∂(coordW (Fv F v) b lam 1 n) = (latV b v).indicator 1 Y := by
    intro Y
    by_cases hY : Y ∈ latV b v
    · have hf : (fun a : Fin 1 → Fin n → Fv F v ⊗[F] E =>
          (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ (hypOne J) g (consA a Y))) =
          (latV b v).indicator 1 := by
        funext a
        by_cases ha : a ∈ latV b v
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem
            ((actW_mem_iff σ _ b v g hg _).2 ((consA_mem_iff hv a Y).2 ⟨ha, hY⟩))]
          rfl
        · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem
            fun hc => ha ((consA_mem_iff hv a Y).1 ((actW_mem_iff σ _ b v g hg _).1 hc)).1]
      rw [hf, lintegral_indicator_one (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM b 1 n v), hmass,
        Set.indicator_of_mem hY]
      rfl
    · have hf : (fun a : Fin 1 → Fin n → Fv F v ⊗[F] E =>
          (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ (hypOne J) g (consA a Y))) = 0 := by
        funext a
        exact Set.indicator_of_notMem
          (fun hc => hY ((consA_mem_iff hv a Y).1 ((actW_mem_iff σ _ b v g hg _).1 hc)).2) _
      rw [hf, Set.indicator_of_notMem hY, lintegral_zero_fun]
  unfold stageInt
  simp_rw [hin]
  exact lintegral_indicator_one (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM b n M v)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetMapSurjectiveWhittakerStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_jacquet_map_surjective_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ J : openFns d hd ρ →ₗ[ℂ] W, Function.Surjective J ∧ ∀ f : openFns d hd ρ, J f ∈ twKer ρ (unipM k d) (whitM d ψ) ↔ (f : IndSp (stdBlocks d hd) ρ) ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker | exact GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker | (intros; apply GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairIterPhiMir
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZPairDescend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 2000000 in

theorem pair_iterPhi_mir (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) :
    ∀ (j s : ℕ) (τ τ' : MRep k (n + 1 + j)),
    IsSmooth τ.ρ → IsSmooth τ'.ρ → ∀ B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1 + j)) v v', B (τ.ρ p v) (τ'.ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : (iterPhi k ψ j τ).V →ₗ[ℂ] (iterPhi k ψ⁻¹ j τ').V →ₗ[ℂ] ℂ,
      (∀ (p : Mir k (n + 1)) w w', B' ((iterPhi k ψ j τ).ρ p w) ((iterPhi k ψ⁻¹ j τ').ρ p w') =
        ((detChar (Fin (n + 1 + 1)) (absPow k ((s + j : ℕ) : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0)
  | 0, s, _, _, _, _, B, hB, hn => ⟨B, hB, hn⟩
  | j + 1, s, τ, τ', hs, hs', B, hB, hn => by
    obtain ⟨B₁, hB₁, hn₁⟩ := GlobalTheory.CompanionTheory.MirPair.pairing_phi k ψ hc h1 (n + 1 + j) s _ _ τ.ρ τ'.ρ hs hs' B hB hn
    obtain ⟨B₂, hB₂, hn₂⟩ := pair_iterPhi_mir ψ hc h1 n j (s + 1) (MRep.phiM k ψ τ) (MRep.phiM k ψ⁻¹ τ')
      (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hs) (GlobalTheory.T.smooth_phi_minus k ψ⁻¹ _ _ _ hs') B₁ hB₁ hn₁
    refine ⟨B₂, fun p w w' => ?_, hn₂⟩
    have e : s + (j + 1) = s + 1 + j := by omega
    rw [e]
    exact hB₂ p w w'

set_option maxHeartbeats 2000000 in

theorem pair_iterPhi (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V V' : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (π' : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V') (hs : IsSmooth π) (hs' : IsSmooth π')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π g v) (π' g v') = B v v') (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) :
    ∃ B' : (iterPhi k ψ j (resM k π)).V →ₗ[ℂ] (iterPhi k ψ⁻¹ j (resM k π')).V →ₗ[ℂ] ℂ,
      (∀ (p : Mir k (n + 1)) w w', B' ((iterPhi k ψ j (resM k π)).ρ p w) ((iterPhi k ψ⁻¹ j (resM k π')).ρ p w') =
        ((detChar (Fin (n + 1 + 1)) (absPow k (j : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  have hB0 : ∀ (p : Mir k (n + 1 + j)) v v', B ((resM k π).ρ p v) ((resM k π').ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k ((0 : ℕ) : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v' := by
    intro p v v'
    rw [GlobalTheory.CompanionTheory.BZCuspPair.detChar_zero, one_mul]
    exact hB (p : GL (Fin (n + 1 + j + 1)) k) v v'
  obtain ⟨B', h2, h3⟩ := pair_iterPhi_mir ψ hc h1 n j 0 (resM k π) (resM k π')
    (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hs) (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hs') B hB0 hn
  refine ⟨B', fun p w w' => ?_, h3⟩
  have := h2 p w w'
  rwa [Nat.zero_add] at this

end GlobalTheory.CompanionTheory.BZPairDescend

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_lattice_sum_bounded : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n →
    Continuous φ ∧ ∃ B : ℝ≥0, ∀ w : Mx D m n, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖φ (rat ξ + w)‖ₑ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | exact GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetClosedOpenSequenceStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_closed_open_sequence : ∀ {G M Z VC VO AC AO : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup VC] [Module ℂ VC] [AddCommGroup VO] [Module ℂ VO]
    [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (s : M →* G) (c : M →* ℂˣ) (ρ : Representation ℂ M (TwJacquet (cInd H σ) U θ))
    (hρ : ∀ (m : M) (f : cIndSpace H σ), ρ m (Submodule.Quotient.mk f) =
      ((c m : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd H σ (s m) f))
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hCU : ∀ x ∈ C, ∀ u ∈ U, x * u ∈ C)
    (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (eC : cIndSpace H σ →ₗ[ℂ] AC) (eO : cIndSpace H σ →ₗ[ℂ] AO)
    (hC1 : ∀ (u : U) f, eC (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eC f)
    (hO1 : ∀ (u : U) f, eO (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eO f)
    (hCs : ∀ m f, aC m (eC f) = ((c m : ℂˣ) : ℂ) • eC (cInd H σ (s m) f))
    (hOs : ∀ m f, aO m (eO f) = ((c m : ℂˣ) : ℂ) • eO (cInd H σ (s m) f))
    (hCmem : ∀ f, ∃ v, jC v = eC f)
    (hOmem : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → ∃ v, jO v = eO f)
    (hConto : ∀ v, ∃ f, eC f = jC v)
    (hOonto : ∀ v, ∃ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) ∧ eO f = jO v)
    (hCoff : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → eC f = 0)
    (hlocC : ∀ f, eC f = 0 → ∀ p ∈ C, AvgVanish H σ U θ f p)
    (hlocO : ∀ f, eO f = 0 → ∀ p, p ∉ C → AvgVanish H σ U θ f p),
  ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Glue.extension | exact GlobalTheory.CompanionTheory.BZPhiPG.Glue.extension | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Glue.extension <;> assumption)
end

