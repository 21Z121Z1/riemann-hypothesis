import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt.Disc

section Gen

variable {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def quotMapEquiv (e : V ≃ₗ[R] W) (A L : Submodule R V) (A' L' : Submodule R W) (hA : A.map (e : V →ₗ[R] W) = A')
    (hL : L.map (e : V →ₗ[R] W) = L') : (A ⧸ L.comap A.subtype) ≃ₗ[R] (A' ⧸ L'.comap A'.subtype) := by
  subst hA hL
  refine Submodule.Quotient.equiv _ _ (e.submoduleMap A) ?_
  ext ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨z, hz, hze⟩
    have : (z : V) = x := e.injective (congrArg Subtype.val hze)
    exact ⟨x, this ▸ hz, rfl⟩
  · rintro ⟨x', hx', hxe⟩
    have : x' = x := e.injective hxe
    subst this
    exact ⟨⟨x', hx⟩, hx', rfl⟩

end Gen

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {Pr.piT u} = ⨅ P : Pr.vT u, P.1.asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact decoFin_mem_of_mem_divs P.2
  · exact Ideal.mem_span_singleton.2 (piT_dvd_of_mem hX hPr u r fun P => Ideal.mem_iInf.1 hr P)

theorem span_conj_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {X.conjO (Pr.piT u)} = ⨅ P : Pr.vT u, (conjPrime₂ P.1).asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show cO X.E (X.conjO (Pr.piT u)) ∈ P.1.asIdeal
    rw [show cO X.E (X.conjO (Pr.piT u)) = Pr.piT u from cO_cO _]
    exact decoFin_mem_of_mem_divs P.2
  · obtain ⟨s, hs⟩ := piT_dvd_of_mem hX hPr u (cO X.E r) fun P => Ideal.mem_iInf.1 hr P
    refine Ideal.mem_span_singleton.2 ⟨cO X.E s, ?_⟩
    have := congrArg (cO X.E) hs
    rw [cO_cO, map_mul] at this
    exact this

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_T_eq {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)} = Ideal.span {Pr.piT u} ⊓ Ideal.span {X.conjO (Pr.piT u)} := by
  rw [← hPr.piT_norm u, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.mul_eq_inf_of_coprime ((Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)).sup_eq

theorem quotT_equiv {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Nonempty ((𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃ₗ[𝓞 X.E]
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal))) := by
  have hco : IsCoprime (Ideal.span {Pr.piT u}) (Ideal.span {X.conjO (Pr.piT u)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)
  have hp1 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => P.1.asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne P.1.isMaximal Q.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hp2 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => (conjPrime₂ P.1).asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (conjPrime₂ P.1).isMaximal (conjPrime₂ Q.1).isMaximal fun h => hne (Subtype.ext ?_)
    ext x
    have h2 := congrArg (fun J : Ideal (𝓞 X.E) => cO X.E x ∈ J) h
    simp only [conjPrime₂, Ideal.mem_comap, cO_cO] at h2
    exact Iff.of_eq h2
  let φ : (𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃+*
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal)) :=
    (Ideal.quotEquivOfEq (span_T_eq hPr u)).trans ((Ideal.quotientInfEquivQuotientProd _ _ hco).trans
      (RingEquiv.prodCongr
        ((Ideal.quotEquivOfEq (span_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp1))
        ((Ideal.quotEquivOfEq (span_conj_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp2))))
  exact ⟨(AlgEquiv.ofRingEquiv (f := φ) fun a => rfl).toLinearEquiv⟩

end GlobalTheory.Mem.Col2.HAt.Disc

open GlobalTheory.Mem.Col2.HAt.Disc in

theorem GlobalTheory.Mem.Col2.TC.disc_cl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  intro B X I hI hP l Z H F _ _ u i hi c
  obtain ⟨hG, -, hc⟩ := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hL : latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c) = ((I.stp u I.mu0 i).rep c).1.1.deco.1.L := (hc u I.mu0).1 c
  have hD : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i c) =
      ((I.stp u I.mu0 i).rep c).1.1.deco.1.Lsh := by
    refine (dual_co (I.rec7 l Z).sp.cm _ (rankN (I.rec7 l Z) i hi) _).trans ?_
    have h1 := BwLat.dualL_std (E := B.host.E) (sigD (I.rec7 l Z)).toRingHom (fun x => rfl) ((I.stp u I.mu0 i).rep c).1.1.deco.1.L
    exact (congrArg₂ (dualL _) hG hL).trans h1
  have hc' : ∀ P Q : (B.primes X).vT u, Q.1 ≠ conjPrime₂ P.1 := fun P Q => (moveHyp_of_ok l.pr u P).st Q
  obtain ⟨e1⟩ := ((I.stp u I.mu0 i).rep c).1.1.deco.2.Lsh_quot_L hc'
  obtain ⟨e2⟩ := quotT_equiv (FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u
  exact ⟨(quotMapEquiv ((crdN (I.rec7 l Z) i hi).restrictScalars (𝓞 (I.rec7 l Z).host.E)) _ _ _ _ hD hL) ≪≫ₗ e1 ≪≫ₗ e2.symm⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexificationOfDefiniteGroupForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem eq_sum_single {R : Type} [Semiring R] (a : MonoidAlgebra R G) : a = ∑ g, single g (a.coeff g) := by
  classical
  apply MonoidAlgebra.ext
  ext g
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

noncomputable def conjSum (R : Type) [Semiring R] (g : G) : MonoidAlgebra R G := ∑ h, single (h * g * h⁻¹) 1

theorem conjSum_mem_center (R : Type) [CommSemiring R] (g : G) : conjSum R g ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of k =>
    simp only [conjSum, MonoidAlgebra.of_apply, Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    congr 1
    group
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapRange_conjSum {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (g : G) :
    mapRingHom G f (conjSum R g) = conjSum S g := by
  simp [conjSum, map_sum, MonoidAlgebra.mapRangeRingHom_single]

theorem card_smul_eq {R : Type} [CommSemiring R] (z : MonoidAlgebra R G) (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    (Fintype.card G : R) • z = ∑ g, z.coeff g • conjSum R g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = z := fun h => by
    rw [hz, mul_assoc, single_mul_single, mul_inv_cancel, one_mul, ← one_def, mul_one]
  have h2 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = ∑ g, single (h * g * h⁻¹) (z.coeff g) := fun h => by
    conv_lhs => rw [eq_sum_single z]
    simp only [Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
  calc (Fintype.card G : R) • z = ∑ h : G, z := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : G, ∑ g, single (h * g * h⁻¹) (z.coeff g) := Finset.sum_congr rfl fun h _ => (h1 h).symm.trans (h2 h)
    _ = ∑ g, z.coeff g • conjSum R g := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [conjSum, Finset.smul_sum, smul_single, smul_eq_mul, mul_one]

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mapRingHom {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (a : MonoidAlgebra R G) (g : G) :
    (mapRingHom G f a).coeff g = f (a.coeff g) := by
  classical
  conv_lhs => rw [eq_sum_single a]
  simp [map_sum, MonoidAlgebra.mapRangeRingHom_single, MonoidAlgebra.coeff_sum, Finsupp.single_apply, apply_ite f]

section Act

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {σ : K →+* ℂ}
  {j : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n)} {H : Matrix (Fin n) (Fin n) K}
  {ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n))}

theorem rho_smul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (c : K) (E : Matrix (Fin n) (Fin n) K) :
    ρ (c • E) = σ c • ρ E := by
  refine LinearMap.ext_on_range (hρ E).span fun i => ?_
  rw [(hρ _).op_eq, LinearMap.smul_apply, (hρ E).op_eq, Matrix.smul_mulVec, map_smulₛₗ]

theorem rho_symm (hρ : ∀ E, FormsTie σ j H E (ρ E)) (E : Matrix (Fin n) (Fin n) K)
    (hsa : ∀ x y, Formalism.DivisionValues.hform H (E.mulVec x) y = Formalism.DivisionValues.hform H x (E.mulVec y)) : (ρ E).IsSymmetric := by
  let b := Module.Basis.mk (hρ E).li (hρ E).span.ge
  have hB : (innerₛₗ ℂ).comp (ρ E) = (innerₛₗ ℂ).compl₂ (ρ E) := by
    refine LinearMap.ext_basis b b fun i k => ?_
    simp only [b, Module.Basis.mk_apply, LinearMap.comp_apply, LinearMap.compl₂_apply, (hρ E).op_eq]
    change inner ℂ (j _) (j _) = inner ℂ (j _) (j _)
    rw [(hρ E).inner, (hρ E).inner, hsa]
  intro x y
  have := DFunLike.congr_fun (DFunLike.congr_fun hB x) y
  exact this

noncomputable def lin (ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)))
    (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K) :
    MonoidAlgebra ℂ G →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun a := ∑ g, a.coeff g • ρ (op (single g 1))
  map_add' a b := by simp [MonoidAlgebra.coeff_add, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [MonoidAlgebra.coeff_smul, Finset.smul_sum, smul_smul]

theorem lin_map (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a) (a : MonoidAlgebra K G) :
    lin ρ op (mapRingHom G σ a) = ρ (op a) := by
  let opL : MonoidAlgebra K G →ₗ[K] Matrix (Fin n) (Fin n) K := ⟨⟨op, hadd⟩, hsmul⟩
  change _ = ρ (opL a)
  conv_rhs => rw [eq_sum_single a]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : single g (a.coeff g) = a.coeff g • single g (1 : K) := by rw [smul_single, smul_eq_mul, mul_one]
  rw [h1, map_smul, rho_smul hρ, coeff_mapRingHom]
  rfl

theorem lin_mul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b)
    (z w : MonoidAlgebra ℂ G) (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (hw : w ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : lin ρ op (z * w) = lin ρ op z * lin ρ op w := by
  have hone : ∀ α : G → ℂ, lin ρ op (∑ g, α g • conjSum ℂ g) = ∑ g, α g • ρ (op (conjSum K g)) := fun α => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, ← mapRange_conjSum σ, lin_map hρ op hadd hsmul]
  have key : ∀ α β : G → ℂ, lin ρ op ((∑ g, α g • conjSum ℂ g) * ∑ h, β h • conjSum ℂ h) =
      lin ρ op (∑ g, α g • conjSum ℂ g) * lin ρ op (∑ h, β h • conjSum ℂ h) := fun α β => by
    rw [hone, hone, Finset.sum_mul_sum, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm, map_smul, ← mapRange_conjSum σ, ← mapRange_conjSum σ, ← map_mul,
      lin_map hρ op hadd hsmul, hmul _ (conjSum_mem_center K g) _ (conjSum_mem_center K h), map_mul]
  have h := key z.coeff w.coeff
  rw [← card_smul_eq z hz, ← card_smul_eq w hw, smul_mul_smul_comm, map_smul, map_smul, map_smul,
    smul_mul_smul_comm] at h
  have hc : ((Fintype.card G : ℂ) * (Fintype.card G : ℂ)) ≠ 0 := by
    have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact mul_ne_zero this this
  exact smul_right_injective _ hc h

noncomputable def actC (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b) (hone : op 1 = 1) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun z := lin ρ op z
  map_one' := by
    change lin ρ op 1 = 1
    rw [← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one]
  map_mul' z w := lin_mul hρ op hadd hsmul hmul z w z.2 w.2
  map_zero' := map_zero _
  map_add' z w := map_add _ _ _
  commutes' c := by
    change lin ρ op (algebraMap ℂ (MonoidAlgebra ℂ G) c) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one,
      Algebra.algebraMap_eq_smul_one]

end Act

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

theorem exists_complexification_of_definiteGroupForms : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (m : Mat1 K G) (e : MonoidAlgebra K G), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (∀ y, IsIntegral ℤ (o y)) → m.Laws σ e → ∃ s : Sp1 O (σ.comp o) G, Nonempty (Tie1 σ m s) := by
  intro K O _ _ _ _ o σ G _ _ m e hσ ho hm
  obtain ⟨j, M, ρ, hρ, hM, hcar⟩ :=
    GlobalTheory.Mem.CoordForms.exists_formsTie_oLatTie K O o σ m.n m.H m.N hσ hm.pos hm.lat
  have hcar' := hcar ho
  have hEE : m.E * m.E = m.E := by
    rw [hm.E_eq, ← hm.mul e hm.cen e hm.cen, hm.idem.eq]
  let s : Sp1 O (σ.comp o) G :=
    { A := Hs.mk (EuclideanSpace ℂ (Fin m.n))
      lat := M
      e := ρ m.E
      idem := by rw [← Module.End.mul_eq_comp, ← map_mul, hEE]
      sa := rho_symm hρ m.E hm.sa
      act := actC hρ m.op hm.add hm.smul hm.mul hm.one }
  refine ⟨s, ⟨{ j := j, forms := hρ m.E, latT := hM, stable := ?_, cen := ?_ }⟩⟩
  · intro a y hy
    change y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n))) at hy
    change σ (a : K) • y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n)))
    rw [hcar'] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨(a : K) • x, ?_, by rw [map_smulₛₗ]⟩
    have := m.N.smul_mem a hx
    rwa [← algebraMap_smul K] at this
  · intro z a hza x
    have hz : (z : MonoidAlgebra ℂ G) = mapRingHom G σ a := by
      apply MonoidAlgebra.ext
      ext g
      rw [coeff_mapRingHom]
      exact (hza g).symm
    change lin ρ m.op z (j x) = _
    rw [hz, lin_map hρ m.op hm.add hm.smul, (hρ _).op_eq]

end GlobalTheory.Mem.R3.Rw.SpOfMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharactersStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_core_laws_for_replaced_hecke_characters : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  first | exact @GlobalTheory.RealGeo.exists_mu_reCore | exact GlobalTheory.RealGeo.exists_mu_reCore | (intros; apply GlobalTheory.RealGeo.exists_mu_reCore <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiamondElementsStepLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

theorem exists_int_isDia {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
      ∀ {n f : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
        (S : StepLevel D.host.F D.host.E (sigD D) J (D.mem u).A.T f bad), ∃ δ, IsDia S (A.eV v).1 (A.eV v).2 k δ := by
  obtain ⟨k, hk, hkT⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied A v
  exact ⟨k, hk, fun S => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.is_diamond_of_local_diamond S _ _ k
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent S _ _ (D.mem u).A.T_prime k hkT e he hee hσ)⟩

set_option maxHeartbeats 1000000 in

theorem exists_isDia_steps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : ((I.rec7 l Z).mem u).A.Fv v) = a ∧ (∀ h : i = 0 ∨ i = (I.rec7 l Z).R.m, ∃ δ, IsDia ((F u).cls i hi h).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ) ∧ ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), ∃ δ, IsDia ((F u).ch i h1 h2 β).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ := by
  intro B X I _ _ l Z H F _ _ u i hi v a
  obtain ⟨k, hk, h⟩ := exists_int_isDia (F u).atT v a
  exact ⟨k, hk, fun _ => h _, fun _ _ _ => h _⟩

end GlobalTheory.Mem.Col2.HAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageOfPk
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def bkMk {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (b : ∀ u, (C.fm u).ramSub → (Fin m → B.LL) → B.LL)
    (hb : ∀ u φ x, B.embLL (b u φ x) = W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x))
    (u : B.Word) : (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  LinearMap.mk₂ B.LL (b u)
    (fun φ ψ x => B.embLL.injective (by
      rw [map_add, hb, hb, hb, map_add, (W.Bu_linL u _).map_add]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linL u _).map_smul, smul_eq_mul]))
    (fun φ x y => B.embLL.injective (by
      rw [map_add, hb, hb, hb, map_add, (W.Bu_linR u _).map_add]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linR u _).map_smul, smul_eq_mul]))

open Classical in

def bkOf {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE) (u : B.Word) :
    (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  if H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL then
    bkMk W c (fun u φ x => (H u φ x).choose) (fun u φ x => (H u φ x).choose_spec) u
  else 0

theorem bkOf_spec {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL)
    (u : B.Word) (φ : (C.fm u).ramSub) (x : Fin m → B.LL) :
    W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) = B.embLL (bkOf W c u φ x) := by
  classical
  unfold bkOf
  rw [dif_pos H]
  exact (H u φ x).choose_spec.symm

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def prescribedRowLat {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (jE : (Fin m → B.LL) →ₛₗ[B.embLL] W.EE) :
    Submodule (𝓞 B.LL) (Fin m → B.LL) where
  carrier := {x | ∀ w : W.what₂.places.Pl, ∃ d : 𝓞 B.LL, d ∉ (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 B.LL) {y | jE y ∈ W.what₂.RRset (W.what₂.muAt w)}}
  add_mem' := by
    intro x y hx hy w
    obtain ⟨a, ha, hax⟩ := hx w
    obtain ⟨b, hb, hby⟩ := hy w
    refine ⟨a * b, fun h => ((w : HeightOneSpectrum (𝓞 B.LL)).isPrime.mem_or_mem h).elim ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hax
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hby
  zero_mem' := fun w => ⟨1, (Ideal.ne_top_iff_one _).1 (w : HeightOneSpectrum (𝓞 B.LL)).isPrime.ne_top, by simp⟩
  smul_mem' := by
    intro s x hx w
    obtain ⟨a, ha, hax⟩ := hx w
    exact ⟨a, ha, by rw [smul_comm]; exact Submodule.smul_mem _ _ hax⟩
end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

theorem exists_divStage_of_pk : ∀ (B : Base) (C : Cols B) (G : Type) [Group G] (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (n : Nums p W₀) (η : ℕ → B.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w), (∀ v, IsUnit (p.Xo v).det) → ∀ (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V) (h : B.Word → ℝ) (etaF : ℝ), ∃ V : DivStage B C (p.what₂ e W₀ n η hη), DivIs p V ∧ (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧ V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax ∧ ((∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) ∈ Set.range B.embLL) → ∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) = B.embLL (V.div.Bk u φ x)) := by
  intro B C G _ p e W₀ n η hη hXo Ln h etaF
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL (p.what₂ e W₀ n η hη).EE p.nR p.cR ⊥
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin p.nR) (Fin p.nR) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v
  let Lr : Submodule (𝓞 B.LL) (Fin p.nR → B.LL) :=
    prescribedRowLat (p.what₂ e W₀ n η hη) (GlobalTheory.Mem.coordForm B.embLL p.cR)
  let RR : HLat B.LL :=
    { V := Fin p.nR → B.LL, ι := Fin p.nR, b := Pi.basisFun B.LL (Fin p.nR), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let Dd : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := bkOf (p.what₂ e W₀ n η hη) p.cR, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := p.Dall, delP := p.delp,
      delP_le_one := p.delp_le_one }
  let V : DivStage B C (p.what₂ e W₀ n η hη) :=
    { div := Dd
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := GlobalTheory.Mem.coordForm B.embLL p.cR
      jEE_basis := by
        have : (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) = p.cR :=
          funext (GlobalTheory.Mem.coordForm_basisFun B.embLL p.cR)
        show LinearIndependent ℂ (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) ∧
          Submodule.span ℂ (Set.range (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i))) = ⊤
        rw [this]
        exact ⟨p.cR.linearIndependent, p.cR.span_eq⟩
      jN := GlobalTheory.Mem.ramForm (p.what₂ e W₀ n η hη)
      jN_basis := fun u => GlobalTheory.Mem.ramForm_basis (p.what₂ e W₀ n η hη) u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => GlobalTheory.Mem.eMu_ramForm (p.what₂ e W₀ n η hη) u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin p.nR)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, ⟨⟨LinearEquiv.refl _ _, fun x => rfl, fun v hv x y => ?_⟩, fun S N G' => ?_⟩,
    fun u x => Iff.rfl, rfl, rfl, rfl, fun H u φ x => bkOf_spec (p.what₂ e W₀ n η hη) p.cR H u φ x⟩
  · show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) p.Xo v x y
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]
  · intro x
    simp only [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_RRset]
    exact Iff.rfl

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  first | exact @GlobalTheory.exists_equiv_normAt_eq_norm | exact GlobalTheory.exists_equiv_normAt_eq_norm | (intros; apply GlobalTheory.exists_equiv_normAt_eq_norm <;> assumption)
end

