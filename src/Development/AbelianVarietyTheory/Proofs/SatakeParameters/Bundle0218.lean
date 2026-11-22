import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0209
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.SplitEigen

theorem exists_eigen_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible)
    (f : ι → U →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (c : G → ℂ) (φ : V) (h0 : φ ≠ 0)
    (hK : ∀ k ∈ K, ρ k φ = c k • φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - c k • v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add] at h5
          have h6 : f i (σ k v - c k • v) = c k • x - ρ k x := by
            rw [map_sub, hf, map_smul]; rw [smul_add] at h5; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem (W.smul_mem _ hx) (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add, ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

theorem exists_locComp_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  classical
  intro E _ _ _ n U hU w hw J _ _ χ φ hφ h0 hχ
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨σ, -, hσ, -⟩ := GlobalTheory.DefU.exists_locComp_split E n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let p : locU n w →* GL (Fin n) (w.adicCompletion E) := (cLoc w).comp (locU n w).subtype
  have hp : p = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  let σ' : Representation ℂ (locU n w) σ.V := σ.ρ.comp p
  have hirr : σ'.IsIrreducible := by
    change Representation.IsIrreducible (σ.ρ.comp p); rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨-, f, hf0, hfm, hf⟩ := hσ
  let F : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hsup := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype
    σ' σ' π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
  let c : locU n w → ℂ := fun k => if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_mem_iSup (π.rep.comp (locU n w).subtype) σ' hirr
    (fun h : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
    (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
    {k | cLoc w (k : UA E n) ∈ J} c ⟨φ, hφ⟩
    (fun h => h0 (congrArg Subtype.val h))
    (fun k hk => Subtype.ext (by
      change RU E n (k : UA E n) φ = c k • φ
      show RU E n (k : UA E n) φ = (if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0) • φ
      have hk' : cLoc w (k : UA E n) ∈ J := hk
      rw [dif_pos hk']
      exact hχ _ k.2 hk'))
    (hsup ▸ Submodule.mem_top)
  refine ⟨v, hv0, fun g => ?_⟩
  have hk : cLoc w ((e.symm g : locU n w) : UA E n) ∈ J := by rw [hcl]; exact g.2
  have h1 := hv (e.symm g) hk
  have h2 : σ' (e.symm g) = σ.ρ g := by
    change σ.ρ (cLoc w ((e.symm g : locU n w) : UA E n)) = _
    rw [hcl]
  rw [h2] at h1
  rw [h1]
  simp only [c, dif_pos hk]
  congr 3
  exact Subtype.ext (hcl g)

end GlobalTheory.SplitEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNhdsOnePrincipalCongruenceSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCongNbhd

theorem conjAL_entry (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j)
      = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hx : ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h3 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
    calc _ = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
            rw [hx, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [h2]; simp [conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem ringHom_one_apply {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.SplitCongNbhd

open GlobalTheory.SplitCongNbhd in

theorem GlobalTheory.SplitCongNbhd.exists_nhds_one_cong (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (N : ℕ) (hN : 0 < N) :
    ∃ U ∈ nhds (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))),
      ∀ x : GAf L n, TrivOutside {s.v} x → s.loc n x ∈ U → NG.Cong L n N x := by
  set K := s.v.adicCompletion (maximalRealSubfield L)
  let U : Set (GL (Fin n) K) := {A | ∀ i j,
    Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
    Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
      (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1}
  refine ⟨U, ?_, ?_⟩
  · have hball : {t : K | Valued.v t ≤ 1} ∈ nhds (0 : K) :=
      (Valued.isOpen_integer K).mem_nhds (by simp [Valuation.mem_integer_iff])
    have key : ∀ f : GL (Fin n) K → K, Continuous f → f 1 = 0 →
        ∀ᶠ A in nhds (1 : GL (Fin n) K), Valued.v (f A) ≤ 1 := by
      intro f hf h1
      exact hf.continuousAt.preimage_mem_nhds (by rw [h1]; exact hball)
    have hc1 : ∀ i j, Continuous fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_val.matrix_elem i j
    have hc2 : ∀ i j, Continuous fun A : GL (Fin n) K =>
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_coe_inv.matrix_elem i j
    have hij : ∀ i j, ∀ᶠ (A : GL (Fin n) K) in nhds 1,
        Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
        Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
          (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 := fun i j =>
      (key _ (continuous_const.mul ((hc1 i j).sub continuous_const)) (by simp)).and
        (key _ (continuous_const.mul ((hc2 i j).sub continuous_const)) (by simp))
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  · intro x hx hU
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitSep.exists_sep L s
    have hN' : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
    set c : AL L := ((N : L)⁻¹) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hc
    have hNc : (N : AL L) * c = 1 := by
      rw [hc, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hN',
        one_mul]; rfl
    have hconjc : conjAL L c = c := by
      rw [hc, GlobalTheory.SplitLift.conjAL_tmul, map_inv₀, map_natCast]
    have hprojc : s.proj c = (N : K)⁻¹ := by
      rw [hc, GlobalTheory.SplitLift.proj_tmul, map_inv₀, map_natCast]; simp
    set M : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hM
    have hy : ∀ i j, c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) ∈ ALint L := by
      intro i j
      refine GlobalTheory.mem_ALint_of_supported_at_split L s e he1 he2 _ ?_ ?_ ?_
      · intro w hw
        have h1 := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h1
        rw [map_mul, map_sub, h1, ringHom_one_apply, sub_self, mul_zero]
      · rw [map_mul, map_sub, hprojc, ringHom_one_apply]
        exact (hU i j).1
      · have hinv : s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((((s.loc n x)⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j i := by
          rw [← map_inv]; rfl
        have h1 : (1 : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) j i := by
          simp [Matrix.one_apply, eq_comm]
        rw [map_mul, map_sub, hconjc, hM, conjAL_entry, ringHom_one_apply, map_mul, map_sub, hprojc, hinv,
          ringHom_one_apply, h1]
        exact (hU j i).2
    have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      intro i j; rw [Matrix.one_apply]; split_ifs
      · exact (ALint L).one_mem
      · exact (ALint L).zero_mem
    have hz : ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) := by
      intro i j; rw [← mul_assoc, hNc, one_mul]
    refine ⟨?_, fun i j => ⟨_, hy i j, hz i j⟩⟩
    show ∀ i j, M i j ∈ ALint L
    intro i j
    have : M i j = (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) +
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j := by rw [← hz, sub_add_cancel]
    rw [this]
    exact (ALint L).add_mem ((ALint L).mul_mem (natCast_mem _ _) (hy i j)) (hone i j)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.Pst.TwistLetters.Invert

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

theorem mulB_assoc (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (mulB P V y' w) = mulB P V (mulB P (Fin 1 → ↥L.1) y y') w := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v c =>
        rw [mulB_tmul, mulB_tmul, mulB_tmul, mulB_tmul, Pi.smul_apply, smul_eq_mul, mul_smul, mul_assoc]
      | add w w' hw hw' => simp only [map_add, hw, hw']
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

theorem mulB_comm (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    mulB P (Fin 1 → ↥L.1) y y' = mulB P (Fin 1 → ↥L.1) y' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      rw [mulB_tmul, mulB_tmul, mul_comm b b']
      congr 1
      funext i
      rw [Subsingleton.elim i 0]
      simp [mul_comm]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

theorem one_mulB (w : V ⊗[ℚ_[l]] Bst P) :
    mulB P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [mulB_tmul, one_smul, one_mul]
  | add w w' hw hw' => simp only [map_add, hw, hw']

variable {K : FinExt l}

theorem stRep_twist (ρs ρt : Representation ↥L.1 ↥(GK K) V) (χ : ↥(GK K) → ↥L.1)
    (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K)) (w : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g w = χ g • stRep P ρs g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [stRep_tmul, stRep_tmul, ht, TensorProduct.smul_tmul']
  | add w w' hw hw' => simp only [map_add, smul_add, hw, hw']

theorem stRep_trivial_one (g : ↥(GK K)) :
    stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) =
      (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  rw [stRep_tmul, map_one]
  rfl

end GlobalTheory.Pst.TwistLetters.Invert

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.Pst.TwistLetters.Invert in

theorem GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht y y' hinv z
  have hmτ : ∀ g w, stRep P ρm g w =
      χ g • stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w :=
    stRep_twist _ ρm χ (fun g v => by rw [hm]; rfl)
  have hτmul : ∀ g (a w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P),
      stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (mulB P (Fin 1 → ↥L.1) a w) =
        mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a)
          (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w) := fun g a w =>
    stRep_mulB _ _ _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hsmul : ∀ g (a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P),
      stRep P ρs g (mulB P V a w) =
        mulB P V (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a) (stRep P ρs g w) :=
    fun g a w => stRep_mulB ρs ρs _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hτe := stRep_trivial_one (P := P) (L := L) (K := K)
  have hone : ∀ w : V ⊗[ℚ_[l]] Bst P, mulB P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hone' : ∀ w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P,
      mulB P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hχ : ∀ g, χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g⁻¹ * g) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by simp
    rw [map_mul, Module.End.mul_apply, hm, hm, h0] at h1
    have := congrFun h1 0
    simp at this
  have hcomm1 : ∀ a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, mulB P (Fin 1 → ↥L.1) a ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = a := fun a => by
    rw [mulB_comm, hone']
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρm).mp y.2
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρt).mp z.2
  have hx : mulB P V y' (z : V ⊗[ℚ_[l]] Bst P) ∈ Dpst P ρs := by
    refine (mem_Dpst P ρs).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
    have hy := h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)
    have hz := h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    have hc := hχ g
    have hτy : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      rw [hmτ] at hy
      conv_rhs => rw [← hy]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hprod : mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = χ g • ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      have h3 := congrArg (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g) hinv
      rw [hτmul, hτy, hτe, mulB_smul] at h3
      rw [← h3, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hτy' : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = χ g • y' := by
      calc stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = mulB P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hone']
        _ = mulB P (Fin 1 → ↥L.1) (mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hinv]
        _ = mulB P (Fin 1 → ↥L.1) y' (mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
          rw [← mulB_assoc, mulB_comm (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)]
        _ = χ g • y' := by rw [hprod, mulB_smul, hcomm1]
    have hsz : stRep P ρs g (z : V ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (z : V ⊗[ℚ_[l]] Bst P) := by
      rw [stRep_twist ρs ρt χ ht] at hz
      conv_rhs => rw [← hz]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hsmul, hτy', hsz, mulB_smul, mulB_smul_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
  rw [coe_dmul, mulB_assoc, mulB_comm, hinv, hone]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PstConj

open TensorProduct Module GlobalTheory.Pst.EnlargeCoeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'}

theorem tensQ_tensQ (f : V →ₗ[ℚ_[l]] V') (g : V' →ₗ[ℚ_[l]] V) (hgf : ∀ v, g (f v) = v)
    (x : V ⊗[ℚ_[l]] Bst P) : tensQ P g (tensQ P f x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hgf]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def dpstUrCongr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    DpstUr P ρ ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' :=
  let f : V →ₗ[ℚ_[l]] V' := (e : V →ₗ[LL] V').restrictScalars ℚ_[l]
  let g : V' →ₗ[ℚ_[l]] V := (e.symm : V' →ₗ[LL] V).restrictScalars ℚ_[l]
  have hf : ∀ s v, f (ρ s v) = ρ' s (f v) := he
  have hg : ∀ s v, g (ρ' s v) = ρ s (g v) := fun s v => by
    apply e.injective
    change e (e.symm (ρ' s v)) = e (ρ s (e.symm v))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  { toFun := fun x => toUr P ρ' (dQ P hf ((toUr P ρ).symm x))
    invFun := fun x => toUr P ρ (dQ P hg ((toUr P ρ').symm x))
    map_add' := fun x y => by simp only [map_add]
    map_smul' := fun c x => dQ_mulD P hf c _
    left_inv := fun x => Subtype.ext (tensQ_tensQ P f g (fun v => e.symm_apply_apply v) x.1)
    right_inv := fun x => Subtype.ext (tensQ_tensQ P g f (fun v => e.apply_symm_apply v) x.1) }

theorem isPst_congr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (hV : IsPst P ρ) : IsPst P ρ' := by
  rw [IsPst, ← (dpstUrCongr P e he).rank_eq, hV]
  exact (e.restrictScalars ℚ_[l]).rank_eq

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  intro E Ω _ _ _ _ _ l _ ι a P AI _ w A h O _ _ _ Bw hj r r' p hc hr
  have hr' : IsPstAt P Bw r' := by
    obtain ⟨L₁, r₁, h₁, hp⟩ := hr
    obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
    exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩
  exact ⟨hr', GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr hr'⟩

end GlobalTheory.PstConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineWeilDeligneSpaceRestrictionEquivStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineWeilDeligneSpace_restriction_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  first | exact @GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | exact GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | (intros; apply GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquivStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricLemmaCell_one_block_swap_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), d 1 = 1 →
    ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))), b.1 1 0 = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  first | exact @GlobalTheory.OneBlockCell.cellFunctor_swap_equiv | exact GlobalTheory.OneBlockCell.cellFunctor_swap_equiv | (intros; apply GlobalTheory.OneBlockCell.cellFunctor_swap_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  first | exact @GlobalTheory.VTypeTame.ramified_of_isComp | exact GlobalTheory.VTypeTame.ramified_of_isComp | (intros; apply GlobalTheory.VTypeTame.ramified_of_isComp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsTwistByDeRhamCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumps_twist_by_deRham_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  first | exact @GlobalTheory.TwistJumpsW.jumpsW_twist | exact GlobalTheory.TwistJumpsW.jumpsW_twist | (intros; apply GlobalTheory.TwistJumpsW.jumpsW_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InducedProductCommutesFamilyProductStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedProductCommutes_familyProduct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p u : ℕ) (x : Irr k p) (dτ : Fin (u + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  first | exact @GlobalTheory.ProdReorder.commutes_multiProd | exact GlobalTheory.ProdReorder.commutes_multiProd | (intros; apply GlobalTheory.ProdReorder.commutes_multiProd <;> assumption)
end

