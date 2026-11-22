import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorObjDualRepresents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HomScheme

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem dualTensorHom_lTensor {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N']
    [Module O N'] (g : N →ₗ[O] N') (z : Module.Dual O X ⊗[O] N) (x : X) :
    dualTensorHom O X N' (g.lTensor _ z) x = g (dualTensorHom O X N z x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f n => simp [dualTensorHom_apply]
  | add z w hz hw => simp [map_add, hz, hw]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  {a : OAct O G} {b : OAct O H}

def homEquiv [Module.Finite O X] [Module.Projective O X] (h : IsTensor H b G a (Module.Dual O X))
    (T : Over S) : Pts b T ≃ₗ[O] (X →ₗ[O] Pts a T) :=
  (h.equiv T).symm.trans (dualTensorHomEquiv O X (Pts a T))

theorem homEquiv_pre [Module.Finite O X] [Module.Projective O X]
    (h : IsTensor H b G a (Module.Dual O X)) {T T' : Over S} (u : T' ⟶ T) (y : Pts b T) (x : X) :
    homEquiv h T' (Pts.pre b u y) x = Pts.pre a u (homEquiv h T y x) := by
  simp only [homEquiv, LinearEquiv.trans_apply]
  rw [h.natural_symm]
  exact dualTensorHom_lTensor _ _ x

theorem tensorObj_dual_represents {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]
    {O : Type} [CommRing O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    ∃ u : X → (tensorObj (Module.Dual O X) a ⟶ B),
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) →
          ∃! c : T ⟶ tensorObj (Module.Dual O X) a, ∀ x, c ≫ u x = f x := by
  let M := Module.Dual O X
  let C := tensorObj M a
  let b := tensorAct M a
  let h : IsTensor C b B a M := isTensor M a
  let Φ := homEquiv h
  let u : X → (C ⟶ B) := fun x => (Φ C (Pts.mk b (𝟙 C)) x).hom
  have hnat : ∀ (T : Over S) (c : T ⟶ C) (x : X), (Φ T (Pts.mk b c) x).hom = c ≫ u x := by
    intro T c x
    have := congrArg Pts.hom (homEquiv_pre h c (Pts.mk b (𝟙 C)) x)
    rw [Pts.hom_pre] at this
    rw [← this]
    congr 3
  refine ⟨u, fun x => ?_, fun x y => ?_, fun o x => ?_, fun T f hadd hsmul => ?_⟩
  · refine isMonHom_of_mul_comp _ fun T p q => ?_
    rw [← hnat, ← hnat, ← hnat, Pts.mk_mul, map_add, LinearMap.add_apply, Pts.hom_add]
  · change (Φ C _ (x + y)).hom = _
    rw [map_add, Pts.hom_add]
  · change (Φ C _ (o • x)).hom = _
    rw [map_smul, Pts.hom_smul]
  · let F : X →ₗ[O] Pts a T :=
      { toFun := fun x => Pts.mk a (f x)
        map_add' := fun x y => by rw [hadd]; rfl
        map_smul' := fun o x => by rw [hsmul]; rfl }
    refine ⟨((Φ T).symm F).hom, fun x => ?_, fun c hc => ?_⟩
    · rw [← hnat, Pts.mk_hom, LinearEquiv.apply_symm_apply]
      rfl
    · have : Φ T (Pts.mk b c) = F := by
        ext1 x
        apply Pts.ext
        rw [hnat, hc]
        rfl
      rw [← this, LinearEquiv.symm_apply_apply]
      rfl

theorem exists_homObj_relDim (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (g : ℕ) (hg : SmoothOfRelativeDimension g B.hom)
    {O : Type} [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    ∃ (C : Over S) (_ : GrpObj C) (u : X → (C ⟶ B)), IsAbelianScheme C ∧
      SmoothOfRelativeDimension (Module.finrank O X * g) C.hom ∧
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) → ∃! c : T ⟶ C, ∀ x, c ≫ u x = f x := by
  haveI := hB.comm
  obtain ⟨u, h1, h2, h3, h4⟩ := tensorObj_dual_represents B a X
  exact ⟨_, inferInstance, u, (isTensor (Module.Dual O X) a).isAbelianScheme hB,
    GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul S B O a X g hg, h1, h2, h3, h4⟩

end GlobalTheory.HomScheme
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThPBilinearHeis
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_bilinear_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r), ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → ∀ a b : ℂ, thP X hq bas idx (a • φ + b • φ') P x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ' P x) ∧ (∀ (P' : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (a b : ℂ), thP X hq bas idx φ (a • P + b • P') x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ P' x) ∧ ∀ y : Matrix (Fin n) (Fin r) E, thP X hq bas idx (heisG X bas y φ) P x = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hq idx) (fun z => cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) 0 := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq x hd φ hφ P
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun ψ hψ a b => ?_, fun Q a b => ?_, fun y => ?_⟩
  · have h4 := (thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd ψ hψ).2.1
    have e1 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h2 a 0
    have e2 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h4 b 0
    have e3 := GlobalTheory.Jet.polyDeriv_add_fun P (letterDir X hq idx) (h2.const_smul a) (h4.const_smul b) 0
    unfold thP
    rw [((h3 ψ hψ).1 a b).2, ← e1, ← e2]
    exact e3
  · unfold thP
    rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_add, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul]
  · unfold thP
    rw [funext fun z => (h1 y z).2]

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct Topology ComplexOrder

namespace GlobalTheory.ThetaIntegrand

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_princ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (T : Finset (Pl E))
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ PP ∈ T, ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (Ideal.absNorm PP.asIdeal : ℕ) * z) :
    x ∈ St β ∧ ∀ PP ∈ T, redFn β PP x = 1 := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  refine ⟨⟨y, hy⟩, fun PP hP => ?_⟩
  rw [← hy, redFn_frGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨z, hz, e⟩ := h3 PP hP i j
  have e1 : y.1 i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j +
      (Ideal.absNorm PP.asIdeal : ℕ) * ⟨z, hz⟩ := by
    apply Subtype.ext
    have : (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) i j := by
      simp only [Matrix.one_apply]; split_ifs <;> rfl
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, this, ← e, add_sub_cancel]
    rfl
  have e2 : ((Ideal.absNorm PP.asIdeal : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
  change resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [e1, map_add, map_mul, map_natCast, e2, zero_mul, add_zero]
  simp only [Matrix.one_apply]; split_ifs <;> simp

theorem eventually_princ_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Af F)) (T : Finset (Pl E)) {X : Type} [TopologicalSpace X] {x₀ : X}
    {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈ St β ∧
      ∀ PP ∈ T, redFn β PP (Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ)) = 1 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ PP ∈ T, ∀ i j,
      algebraMap F _ ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    rw [Filter.eventually_all_finset]
    simp only [Filter.eventually_all]
    intro PP _ i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_princ β _ T ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro PP hP i j
    refine ⟨_, h3 PP hP i j, ?_⟩
    have hN : ((Ideal.absNorm PP.asIdeal : ℕ) : F) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (Ideal.absNorm PP.asIdeal : ℕ) * (algebraMap F _ ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN, map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

variable {D : D7}

theorem eventually_princ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), finE V κ ∈ UA D.sp.cm V.gram ∧ finE V κ ∈ St β ∧ ∀ PP ∈ T, redFn β PP (finE V κ) = 1 := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) :=
    (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  filter_upwards [eventually_princ_mat β T hf (map_one _)] with κ h
  refine ⟨?_, h⟩
  have := (GlobalTheory.Mass.swapPts (Af D.host.F) D.sp.cm.sig V.gram (π κ)).2
  rwa [GlobalTheory.Mass.coe_swapPts, hπ κ] at this

theorem levFn_eq_one {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n)
    (hg : ∀ PP ∈ L.Pg, redFn β PP x = 1) (hq : ∀ PP ∈ L.Q, redFn β PP x = 1) : levFn β L x = 1 := by
  have h1 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [hg PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [hq PP hP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hg PP hP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

section Generic

variable {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : G →* H) (Γ : Subgroup G)
  (ρ : G →* Module.End ℂ W) {J : Subgroup H} {χ : J →* ℂˣ} {f : H → W}

theorem form_invariant (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ρ (γ * g)⁻¹ (f (π (γ * g))) = ρ g⁻¹ (f (π g)) := by
  have h := hf ⟨γ, hγ⟩ (π g) 1
  rw [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h
  have h' : f (π (γ * g)) = ρ γ (f (π g)) := by rw [map_mul]; exact h
  rw [h', ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem form_continuous [TopologicalSpace G] [IsTopologicalGroup G] (hρ : ∀ x, Continuous fun g => ρ g x)
    (hJ : ∀ᶠ κ in 𝓝 (1 : G), ∃ h : π κ ∈ J, χ ⟨_, h⟩ = 1)
    (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) : Continuous fun g => ρ g⁻¹ (f (π g)) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have h0 : Continuous fun h : G => ρ h⁻¹ (f (π g)) := (hρ _).comp continuous_inv
  refine h0.continuousAt.congr ?_
  have ht : Filter.Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 1) := by
    simpa using (continuous_const_mul g⁻¹).tendsto g
  filter_upwards [ht.eventually hJ] with h hh
  obtain ⟨hk, h5⟩ := hh
  have h4 := hf 1 (π g) ⟨_, hk⟩
  rw [h5, map_one, map_one, Units.val_one, one_smul, one_mul, ← map_mul, mul_inv_cancel_left] at h4
  rw [h4]
  rfl

end Generic

theorem eventually_level (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), ∃ h : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J, (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  classical
  filter_upwards [eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  have hk : finE V κ ∈ lev D.sp.cm V.gram β (flag1L L) :=
    Kg_le_lev (D := flag1L L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩
  exact ⟨hk, levFn_eq_one β (finE V κ) (flag1L L) (fun PP hP => h3 PP (Finset.mem_union_left _ hP))
    fun PP hP => h3 PP (Finset.mem_union_right _ hP)⟩

theorem ext_invariant {V : HSp D} (c : CoefA V) {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ} {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) : ∀ γ ∈ GQ V, ∀ g, c.ext f (γ * g) = c.ext f g :=
  fun _ hγ g => form_invariant (finHom V).rangeRestrict (GQ V) c.ρ hf hγ g

theorem ext_continuous {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1 (eventually_level V β L) hf

theorem integrableOn_form {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) (g : GA D T) :
    IntegrableOn (fun h => thetaKO om h g (pt (io (c.ext f h)))) 𝓕 μ := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io)
    (fun w => hpt _) _ (ext_continuous c hc β L hf) (ext_invariant c hf) μ 𝓕 hμ.1.1 hμ.2 g

theorem thetaIntegrandIntegrable : GlobalTheory.IndefiniteRowSideFullHecke.PinnedIntegrability.ThetaIntegrandIntegrable := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hR i t f hf e g
  obtain ⟨x, hf⟩ := hf
  have hx : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hf' : f = (R.cV i).ext ((R.HV i t).e x) := hf.symm
  have key := integrableOn_form (hR.ωP i t) (D.sp.V_sig _) (hR.vpos i) (R.cV i) (hR.cV i) (R.βV i) (R.datVt i t) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hR.pt_theta i t) (R.ioP i e) (hR.νV i t) g
  rw [← hf'] at key
  exact key

end GlobalTheory.ThetaIntegrand

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPartFibreLieAlgebraCharacters
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorLie

section Grp
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G]

theorem one_left' (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

theorem mul_left_congr {T T' : Over S} (x y : T ⟶ G) (x' y' : T' ⟶ G) (u : Z ⟶ T.left) (u' : Z ⟶ T'.left)
    (hx : u ≫ x.left = u' ≫ x'.left) (hy : u ≫ y.left = u' ≫ y'.left) :
    u ≫ (x * y).left = u' ≫ (x' * y').left := by
  have hb : u' ≫ T'.hom = u ≫ T.hom := by
    rw [← Over.w x, ← Over.w x', ← Category.assoc, ← hx, Category.assoc]
  let U : Over.mk (u ≫ T.hom) ⟶ T := Over.homMk u rfl
  let U' : Over.mk (u ≫ T.hom) ⟶ T' := Over.homMk u' hb
  have e1 : U ≫ x = U' ≫ x' := Over.OverMorphism.ext hx
  have e2 : U ≫ y = U' ≫ y' := Over.OverMorphism.ext hy
  have : U ≫ (x * y) = U' ≫ (x' * y') := by rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2]
  exact congrArg (fun k => k.left) this

end Grp

theorem pull_one_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (T.hom ≫ f) ≫ η[G].left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have hm := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at hm
  have hx : x₀ * x₀ = x₀ := Over.OverMorphism.ext hm
  have h1 : x₀ = 1 := by simpa using hx
  have : x₀.left = (Over.mk (T.hom ≫ f)).hom ≫ η[G].left := by rw [h1, one_left']
  exact this

end GlobalTheory.TorLie

open GlobalTheory.TorLie in
theorem GlobalTheory.torus_part_lie : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  intro S G _ _ O _ act hhom h1 hmul hadd k _ x E
  letI := E.addCommGroup
  haveI := E.i_hom
  set Gx := (Over.pullback x).obj G with hGx
  have hGP := isGrpPullback_pullback G x
  obtain ⟨act', ⟨hhom', h1', hmul', hadd'⟩, hact'⟩ :=
    GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes S (Sp k) x G Gx (pullback.fst G.hom x) hGP O act hhom h1 hmul hadd
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action k Gx E O act' hhom' h1' hmul' hadd'
  obtain ⟨U₀, hinj, hone, hU₀mul, hscale, hequi⟩ := GlobalTheory.T.splitTorus_tangentVectors_addMonoidHom k E.X

  have heq : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt (𝟙 (Sp k))).hom ≫ x := by
    intro l
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w (U₀ l ≫ E.i))
  have hw : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt x).hom := by
    intro l; rw [heq l]; simp [epsPt]
  let U : (E.X →+ k) → (epsPt x ⟶ G) := fun l => Over.homMk _ (hw l)
  have hUl : ∀ l, (U l).left = (U₀ l).left ≫ E.i.left ≫ pullback.fst G.hom x := by
    intro l; simp [U]
  haveI : Mono E.i := E.isKernel.mono_fst_of_mono (IsTerminal.mono_from isTerminalTensorUnit _)
  refine ⟨ρ, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    have hl := congrArg Over.Hom.left h
    rw [hUl, hUl, ← Category.assoc, ← Category.assoc] at hl
    have h2 : (U₀ l ≫ E.i).left = (U₀ l' ≫ E.i).left := by
      apply pullback.hom_ext
      · simpa [Over.comp_left] using hl
      · exact (Over.w (U₀ l ≫ E.i)).trans (Over.w (U₀ l' ≫ E.i)).symm
    exact hinj ((cancel_mono E.i).1 (Over.OverMorphism.ext h2))
  · intro l
    rw [hUl, ← Category.assoc, hone l, ← Category.assoc, ← Over.comp_left, MonObj.one_comp,
      pull_one_left hGP, one_left']
    simp
  · intro l l'
    let x₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l)
    let y₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l')
    have key := hGP.2 (epsPt (𝟙 (Sp k))) (U₀ l ≫ E.i) (U₀ l' ≫ E.i) x₀ y₀ rfl rfl
    rw [← mul_comp, ← hU₀mul] at key
    apply Over.OverMorphism.ext
    have hc := mul_left_congr (U l) (U l') x₀ y₀ (𝟙 _) (𝟙 _) rfl rfl
    simp only [Category.id_comp] at hc
    rw [hc, key, hUl, Over.comp_left, Category.assoc]
  · intro t l
    rw [hUl, hUl, hscale]
    simp [Category.assoc]
  · intro a l
    obtain ⟨τ, hτ, hχ⟩ := hρ a
    have hτl : τ.left ≫ E.i.left = E.i.left ≫ (act' a).left := by
      simpa using congrArg Over.Hom.left hτ
    apply Over.OverMorphism.ext
    have hτU : U₀ l ≫ τ = U₀ (l.comp (ρ a).toAddMonoidHom) := hequi τ (ρ a).toAddMonoidHom (fun χ => hχ χ) l
    rw [Over.comp_left, hUl, hUl, ← hτU, Over.comp_left]
    simp only [Category.assoc, ← hact' a, reassoc_of% hτl]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_not_pairwise_conjugate : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP' := by
  first | exact @GlobalTheory.TypePlaces.not_isConjPl | exact GlobalTheory.TypePlaces.not_isConjPl | (intros; apply GlobalTheory.TypePlaces.not_isConjPl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroupStatement
section
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_doubleCoset_classSum_to_subgroup : ∀ {G H : Type} [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h, ι h = g) → ∀ (T : Subgroup H) (Γ' : Subgroup G), (∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g) → ∀ (K : Subgroup G) (u : G → ℂ), (∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g) → Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)) → (∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) → ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) = ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) := by
  first | exact @GlobalTheory.ClassSumUnfold.unfold_classSum | exact GlobalTheory.ClassSumUnfold.unfold_classSum | (intros; apply GlobalTheory.ClassSumUnfold.unfold_classSum <;> assumption)
end

