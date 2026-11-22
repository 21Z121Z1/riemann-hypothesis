import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaPairingExists
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMatchingTiedRegularizationConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageFactorNonvanishingScalars
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3661
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationKernelOfPIsogenyQuasiInverse
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A), IsUnit ((p : ℕ) : R) → IsPIsog c o o' ψ → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) := by
  first | exact @UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse | exact UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaPairingExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_theta_pairing_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  first | exact @GlobalTheory.GoodFock.exists_good_polynomial | exact GlobalTheory.GoodFock.exists_good_polynomial | (intros; apply GlobalTheory.GoodFock.exists_good_polynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaDiscreteSpace
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem inv_sch (q : ℕ) (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Inv q (sch.obj U) := by
  intro U' ⟨f⟩
  simpa using hU.map f.appTop.hom

theorem pbf_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)),
    Inv q (disc.obj F) → PBF q V := by
  intro q _ N F V hF n i
  obtain ⟨J, ψ, hJ, hinj, he⟩ := GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle q N i
  have key := GlobalTheory.T.injectiveComplexMap_quasiIso_of_unit_schemes q (fun j : Fin N => res (ZMod q) (tw q (i - (j : ℕ)))) J (fun j => 2 * ((j : ℕ) : ℤ)) ψ 0
    (fun j => inferInstanceAs ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.IsStrictlyGE 0)) hJ
    (fun j m => inferInstanceAs (Injective ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.X m))) hinj
    (by
      intro U hU m
      obtain ⟨e, he'⟩ := he (yoneda.obj U) (inv_sch q U hU) m
      have hs := GlobalTheory.T.etaleCohomology_projectiveBundle_formula q U (trivV N (sch.obj U)) (inv_sch q U hU) m i
      have hcomp : (fun a : ∀ j : Fin N, Ht q (sch.obj U) (m - 2 * (j : ℕ)) (i - (j : ℕ)) =>
          ∑ j : Fin N, ((cup q (pull _ (pullback.fst (trivV N (sch.obj U)) (PGL.pr N)) _ _ (a j))
            (cpow q (c1 q (pullback.snd (trivV N (sch.obj U)) (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) :
              Ht q _ m i)) = e ∘ (fun a => ∑ j, cpost _ (ψ j) (m - 2 * (j : ℕ)) m (by omega) (a j)) :=
        funext fun a => (he' a).symm
      rw [hcomp] at hs
      exact (Function.Bijective.of_comp_iff' e.bijective _).1 hs)
    F hF n
  obtain ⟨e, he'⟩ := he F hF n
  rw [GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle N F V]
  have hcomp : pbfMap q (trivV N (disc.obj F)) n i =
      e ∘ (fun a => ∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) :=
    funext fun a => (he' a).symm
  rw [hcomp]
  exact e.bijective.comp key

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSubMemGlueFilIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Coords

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem fstC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e := by
  rw [map_sub, fstC_push, fstC_smul]

theorem sndC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = sndC A₀ e ∘ₗ primPull (dp0 k) (𝟙 _) g - r • sndC A₀ e := by
  rw [map_sub, sndC_push, sndC_smul]

theorem proj_comp_sub {d : ℕ} {M : Type*} [AddCommGroup M] [Module k M] (a : M →ₗ[k] (Fin d → k))
    (P : M →ₗ[k] M) (r : k) (j : Fin d) :
    LinearMap.proj j ∘ₗ (a ∘ₗ P - r • a) = (LinearMap.proj j ∘ₗ a) ∘ₗ P - r • (LinearMap.proj j ∘ₗ a) := by
  ext; simp

set_option maxHeartbeats 2000000 in

theorem push_sub_mem_glueFil_iff {d : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      ∀ j, push (dp0 k) (𝟙 _) g (LinearMap.proj j ∘ₗ sndC A₀ e) - r • (LinearMap.proj j ∘ₗ sndC A₀ e) -
        f j (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [mem_glueFil_iff, fstC_push_sub]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have h0 := sndC_push_sub (V := Fin d → k) g r e
  rw [h0, proj_comp_sub]
  rfl

set_option maxHeartbeats 2000000 in

theorem sub_sum_mem_glueFil_iff {d a : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ∀ j, (LinearMap.proj j ∘ₗ sndC A₀ e - ∑ i, LinearMap.proj j ∘ₗ sndC A₀ (w i)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by
  rw [mem_glueFil_iff, map_sub, map_sum]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have hs : ∀ h : Fin a → (primDR A₀ →ₗ[k] (Fin d → k)),
      LinearMap.proj j ∘ₗ ∑ x, h x = ∑ x, LinearMap.proj j ∘ₗ h x := fun h ↦ by
    ext c; simp [LinearMap.sum_apply]
  rw [map_sub, map_sum, LinearMap.comp_sub, hs]

variable (f : HdR A₀ →ₗ[k] HdR A₀)
  (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
  (hE : ∀ e, e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀))
include hE

set_option maxHeartbeats 2000000 in
theorem push_sub_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - r • (sndC A₀ e : HdR A₀) -
        f (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [hE, fstC_push_sub, sndC_push_sub]
  rfl

set_option maxHeartbeats 2000000 in
theorem push_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - f (push (dp0 k) (𝟙 _) g (fstC A₀ e)) ∈ Fil A₀ := by
  rw [hE, fstC_push, sndC_push]
  rfl

set_option maxHeartbeats 2000000 in
theorem sub_sum_mem_iff {a : ℕ}
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e - ∑ i, w i ∈ E ↔ fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ((sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (w i) : HdR A₀)) - f (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by
  rw [hE, map_sub, map_sub, map_sum, map_sum]

omit hE

end Coords

end GlobalTheory.HTGlueLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleRosatiDescendedActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ a : D.O, LBIso (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (exact GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (intros; apply GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleSymmetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  first | (exact @GlobalTheory.QuasiInvPull.root_symm) | (exact GlobalTheory.QuasiInvPull.root_symm) | (intros; apply GlobalTheory.QuasiInvPull.root_symm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMatchingTiedRegularizationConstantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_matching_tied_regularization_constant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W), ∃ ρ₀ : RealMatch W, ρ₀.vX = ρ.vX ∧ ρ₀.vT = ρ.vT ∧ ρ₀.Tied ∧
    ∀ (i j : Fin D.R.m) (t : T), ∃ c₀ : ℂ, RegConst W B ρ₀ t i j c₀ := by
  first | exact @GlobalTheory.GridFrameExistence.exists_tied | exact GlobalTheory.GridFrameExistence.exists_tied | (intros; apply GlobalTheory.GridFrameExistence.exists_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageFactorNonvanishingScalarsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_factor_nonvanishing_scalars : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W), ρ.Tied → ∀ (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c₀ : ℂ), RegConst W S.B ρ t i j c₀ → c₀ = κ t * lam t := by
  first | exact @GlobalTheory.ThetaRegularizationComparison.regConst_eq | exact GlobalTheory.ThetaRegularizationComparison.regConst_eq | (intros; apply GlobalTheory.ThetaRegularizationComparison.regConst_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageSmallNonzeroBaseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_small_nonzero_base : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
      (∀ t P' h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      ∃ P' : PolF D WW.rank A'.rank, ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @GlobalTheory.StageSmallNz.stage_small_nonzero_zero | exact GlobalTheory.StageSmallNz.stage_small_nonzero_zero | (intros; apply GlobalTheory.StageSmallNz.stage_small_nonzero_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilledStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  first | (exact @GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (exact GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (intros; apply GlobalTheory.DualHomSurj.surjective_of_ker_killed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_translate_eq_twisted_sums : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)) := by
  first | exact @GlobalTheory.GSep.twistSum_translate | exact GlobalTheory.GSep.twistSum_translate | (intros; apply GlobalTheory.GSep.twistSum_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRowStatementsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_row_statements : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @GlobalTheory.RowClaim.JoinF.claims | exact GlobalTheory.RowClaim.JoinF.claims | (intros; apply GlobalTheory.RowClaim.JoinF.claims <;> assumption)
end

