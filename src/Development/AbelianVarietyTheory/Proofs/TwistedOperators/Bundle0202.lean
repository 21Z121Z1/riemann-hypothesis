import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityLeviCharGeometricLemmaCe
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.Exponents

theorem leviChar_unit_injective {R β : Type} [CommRing R] [Fintype β] {χ ψ : β → Rˣ →* ℂˣ}
    (h : leviChar (fun _ : β => Unit) χ = leviChar (fun _ : β => Unit) ψ) : χ = ψ := by
  classical
  funext j
  ext1 x
  have key : ∀ φ : β → Rˣ →* ℂˣ, leviChar (fun _ : β => Unit) φ
      (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar Unit x)) = φ j x := by
    intro φ
    rw [leviChar_apply, Finset.prod_eq_single j]
    · rw [Pi.mulSingle_eq_same]
      congr 1
      ext
      simp
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
    · simp
  rw [← key χ, ← key ψ, h]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_leviChar_of_smooth {β : Type} [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] {χ : β → kˣ →* ℂˣ} (h : ∀ j, IsSmoothChar (χ j)) :
    IsSmoothChar (leviChar c χ) := by
  unfold leviChar
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (h a).detChar.comp _ (continuous_apply a)

theorem nonempty_cell_term_equiv {α β : Type} [Fintype α] [LinearOrder α] [Fintype β]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (g : ∀ j, (Σ i, c i j) ≃ Unit) (s : ∀ i j, IrrRep (GL (c i j) k)) (ψ : α → β → kˣ →* ℂˣ)
    (hψ : ∀ i j, IsSmoothChar (ψ i j)) (e : ∀ i j, Nonempty ((s i j).ρ.Equiv (detRep (c i j) (ψ i j)))) :
    Nonempty ((piTensor fun j => multiProd (g j) fun i => (s i j).ρ).Equiv
      (ofChar (leviChar (fun _ : β => Unit) fun j => ψ ((g j).symm ()).1 j))) := by
  obtain ⟨a⟩ := nonempty_piTensor_detRep_equiv k β (fun _ => Unit) fun j => ψ ((g j).symm ()).1 j
  refine ⟨Representation.Equiv.trans (LocGL.piTensorEquiv fun j => ?_) a⟩
  exact (LocGL.multiProdEquiv (g j) fun i => (e i j).some).trans
    (GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv k α (fun i => c i j) (g j) (fun i => ψ i j) (fun i => hψ i j)).some

theorem jhMult_leviChar_cellFunctor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CellSemisimplification k → ∀ (α β : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ Unit) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), (∀ i, IsSmooth (ρ i)) → (∀ i, HasFiniteLength (ρ i)) → ∀ χ : β → kˣ →* ℂˣ, (∀ j, IsSmoothChar (χ j)) → jhMult (ofChar (leviChar (fun _ : β => Unit) χ)) (cellFunctor (m' := fun _ : β => Unit) f g (piTensor ρ)) = ∏ i, jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := by
  intro k _ _ _ _ hC α β _ _ _ _ m _ _ c _ _ f g X _ _ ρ hρ hl χ hχ
  obtain ⟨T, hT0, hT⟩ := hC α β m (fun _ => Unit) c f g X ρ hρ hl
  have h1 := hT (IrrRep.ofChar (leviChar (fun _ : β => Unit) χ) (isSmoothChar_leviChar_of_smooth _ hχ))
  refine Eq.trans h1 ?_
  let s₀ : ∀ i j, IrrCl (GL (c i j) k) := fun i j => (IrrRep.det (c i j) (χ j) (hχ j)).cl
  have e₀ : ∀ i j, Nonempty ((s₀ i j).rep.ρ.Equiv (detRep (c i j) (χ j))) := fun i j =>
    (IrrRep.det (c i j) (χ j) (hχ j)).nonempty_equiv_rep
  have hfac : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ) (jac (f i) (ρ i)) =
      jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := fun i =>
    jhMult_congr_left ((LocGL.piTensorEquiv fun j => (e₀ i j).some).trans
      (nonempty_piTensor_detRep_equiv k β (c i) χ).some) _
  rw [Finset.sum_eq_single s₀]
  · obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s₀ i j).rep) (fun _ j => χ j)
      (fun _ j => hχ j) e₀
    have h2 : jhMult (ofChar (leviChar (fun _ : β => Unit) χ))
        (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) = 1 :=
      (jhMult_congr_right _ a).trans (jhMult_self (isIrreducible_ofChar _))
    exact (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => hfac i) h2).trans (mul_one _)
  · intro s _ hs
    have hsub : ∀ i j, Subsingleton (c i j) := fun i j =>
      ⟨fun x y => sigma_mk_injective (β := fun i => c i j) ((g j).injective (Subsingleton.elim _ _))⟩
    choose ψ hψ e using fun i j =>
      GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one k (c i j) _ (s i j).rep.ρ (s i j).rep.smooth (s i j).rep.irr
    obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s i j).rep) ψ hψ e
    refine mul_eq_zero_of_right _ ((jhMult_congr_right _ a).trans (Model.jhMult_ofChar_ne fun h => hs ?_))
    have h3 := leviChar_unit_injective h
    funext i j
    have h4 : detChar (c i j) (ψ i j) = detChar (c i j) (χ j) := by
      rcases isEmpty_or_nonempty (c i j) with hc | ⟨⟨x⟩⟩
      · ext1 y
        rw [detChar_apply, detChar_apply, show Matrix.GeneralLinearGroup.det y = 1 from
          Units.ext (by simp), map_one, map_one]
      · have : (g j).symm () = ⟨i, x⟩ := (g j).injective (Subsingleton.elim _ _)
        rw [congrFun h3 j, this]
    rw [← (s i j).cl_rep]
    refine IrrRep.cl_eq_iff.2 ⟨(e i j).some.trans ?_⟩
    show (ofChar (detChar (c i j) (ψ i j))).Equiv (ofChar (detChar (c i j) (χ j)))
    rw [h4]
    exact .refl _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.SmGL.Exponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KernelProjectionPreservesGoodFormsBaseLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

noncomputable section

namespace GlobalTheory.KerProjGood

theorem starProjection_comm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (S : Submodule ℂ V) (T : V →ₗ[ℂ] V) (hT : ∀ u ∈ S, T u ∈ S) (hTa : ∀ u ∈ S, LinearMap.adjoint T u ∈ S) (z : V) :
    (S.starProjection (T z) : V) = T (S.starProjection z) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (Submodule.coe_mem _)) fun w hw => ?_
  rw [← map_sub, ← LinearMap.adjoint_inner_right]
  have h := Submodule.sub_starProjection_mem_orthogonal (K := S) z
  rw [inner_eq_zero_symm]
  exact h _ (hTa w hw)

end GlobalTheory.KerProjGood

open GlobalTheory.KerProjGood in

theorem GlobalTheory.kerProj_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j, ∀ y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j, ((LinearMap.ker ((R.toCx3 F).θ' j A3.A.fam.μ0)).starProjection y : (R.toCx3 F).FLC j A3.A.fam.μ0) ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ hG j y hy
  have hM := hC.base.models
  have hK := RealDat3.kFormL_of (F := F) hM
  have hJ := RealDat3.jIsoL_of (F := F) hM
  set X := R.toCx3 F with hX
  set t := A3.A.fam.μ0
  have sp := lift_embeddings_span hK j t
  have jr : ∀ (g : G) x, X.jL j t ((A3.fam3.F.L j t).r g x) = X.opLC j t (Sum.inr g) (X.jL j t x) :=
    fun g x => X.jL_opL hK j t (Sum.inr g) x

  have hker : ∀ (g : G), ∀ u ∈ LinearMap.ker (X.θ' j t), X.opLC j t (Sum.inr g) u ∈ LinearMap.ker (X.θ' j t) := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    have h := congrArg (fun f => f u) (theta_rho (r := (A3.fam3.F.L j t).r) (ρ := fun g => X.opLC j t (Sum.inr g))
      sp jr (fun g x => hG.2 j t g x) g)
    simp only [LinearMap.comp_apply] at h
    rw [h, hu, map_zero]
  have hadj : ∀ g : G, LinearMap.adjoint (X.opLC j t (Sum.inr g)) = X.opLC j t (Sum.inr g⁻¹) := fun g =>
    (X.opLC_adjoint hK F.cv hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f').symm
  have hcomm : ∀ (g : G) z, ((LinearMap.ker (X.θ' j t)).starProjection (X.opLC j t (Sum.inr g) z) : X.FLC j t) =
      X.opLC j t (Sum.inr g) ((LinearMap.ker (X.θ' j t)).starProjection z) := fun g z =>
    starProjection_comm _ _ (hker g) (fun u hu => by rw [hadj]; exact hker g⁻¹ u hu) z
  have hrange : U2.goodL A3 X F.P0 F.ψ0 F.P1 F.ψ1 j = LinearMap.range (opV A3.fam3.base3.v0.embedding
      (fun g => X.opLC j t (Sum.inr g)) (goodAt (A3.fam3.F.lvlA F.P0 F.ψ0).X (A3.fam3.F.lvlA F.P0 F.ψ0).P
        (A3.fam3.F.lvlA F.P0 F.ψ0).ψ)) := by
    show X.goodPartComplexPoints F.cv false j t = _
    unfold CxData.goodPartComplexPoints
    rw [show F.cv.v0L X.zs false j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA F.P0 F.ψ0) from rfl, goodR_eq]
    conv_rhs => rw [LinearMap.range_eq_map, ← sp, Submodule.map_span]
    congr 1
    ext u
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨X.jL j t x, ⟨x, rfl⟩, (j_opF jr _ x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, j_opF jr _ x⟩
  rw [hrange] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨(LinearMap.ker (X.θ' j t)).starProjection z, ?_⟩
  simp only [opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (hcomm g z).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteDatumIsSchwartzBruhatHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta

theorem isSBHalf_levDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) (levDatum S T βS βT LT Q m e) := by
  intro D S T ΛS ΛT βS βT LT Q m Z e hS hT hfS hfT he
  classical

  have hlin : ∀ (k : ℕ) (u : WO S T), frMapAdj S T βS βT (k • u) = k • frMapAdj S T βS βT u := by
    intro k u
    induction k with
    | zero =>
      have h0 := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT 0 0
      simpa using h0
    | succ n ih =>
      rw [succ_nsmul, GlobalTheory.PlaceVec.frMapAdj_add, ih, succ_nsmul]
  have hadd : ∀ (x u : WO S T) (k : ℕ) i j,
      frMapAdj S T βS βT (x + k • u) i j = frMapAdj S T βS βT x i j + k * frMapAdj S T βS βT u i j := by
    intro x u k i j
    rw [GlobalTheory.PlaceVec.frMapAdj_add, hlin, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]

  have hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True), ∀ i j, (M : EAf D) * frMapAdj S T βS βT u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    obtain ⟨M, hM, hMl⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
    obtain ⟨k, hk, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
    refine ⟨k * M, Nat.mul_pos hk hM, fun u hu i j => ?_⟩
    have hint : IsIntM ((M • u).map (toEAf D)) := by
      intro a b
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, nsmul_eq_mul]
      exact hMl u hu a b
    have h := hup (M • u) hint i j
    rw [hlin, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc] at h
    simpa [Nat.cast_mul] using h

  have hC : ∃ K : ℕ, 0 < K ∧ ∀ t, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) →
      K • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    obtain ⟨k, hk, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
    obtain ⟨K, hK, hKl⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS.1 hT.1
    refine ⟨K * k, Nat.mul_pos hK hk, fun t ht hti => ?_⟩
    have hinf : t.map (infPart D) = 0 :=
      GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)) ht
    have hinf' : (k • t).map (infPart D) = 0 := by
      ext a b
      have h1 := congrFun (congrFun hinf a) b
      rw [Matrix.map_apply, Matrix.zero_apply] at h1
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, h1, smul_zero, Matrix.zero_apply]
    have hint' : ∀ a b, toEAf D ((k • t) a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro a b
      have h2 := hdown t hti a b
      rwa [Matrix.smul_apply, Matrix.map_apply, ← map_nsmul] at h2
    rw [← smul_smul]
    exact hKl (k • t) hinf' hint'

  have hω : ∀ y y' : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)),
      (∀ PP ∈ LT.Pg ∪ Q, y PP = y' PP) →
        omegaG LT m y * omegaQ Q T.rank m (-1) y = omegaG LT m y' * omegaQ Q T.rank m (-1) y' := by
    intro y y' h
    rw [GlobalTheory.PlaceDatum.omegaG_congr LT m y y' (fun PP hP => h PP (Finset.mem_union_left _ hP)),
      GlobalTheory.PlaceDatum.omegaQ_congr Q T.rank m (-1) y y' (fun PP hP => h PP (Finset.mem_union_right _ hP))]
  have key := GlobalTheory.PlaceDatum.isSBHalf_of_red (cA D e)
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (frMapAdj S T βS βT) hadd hB hC (LT.Pg ∪ Q) (fun y => omegaG LT m y * omegaQ Q T.rank m (-1) y) hω
  unfold levDatum
  exact key

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteThetaDatumNeZeroFrameAdjointSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem levDatum_ne_zero_spec {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T) :
    levDatum S T βS βT LT Q m e x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ (∀ PP, PP ∈ LT.Pg ∨ PP ∈ Q → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT x))).det) ∧ ∃ a : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1), (∀ PP : ↥LT.Pg, ((a PP : GL (Fin T.rank) (kP PP.1)) : Matrix (Fin T.rank) (Fin T.rank) (kP PP.1)) = topL T.rank (redM PP.1 (frMapAdj S T βS βT x))) ∧ (∀ PP : ↥LT.Pg, a PP ∈ blockTri (blkOf LT.r LT.t)) ∧ (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H := by
  intro hne
  unfold levDatum at hne
  split_ifs at hne with h0
  · refine ⟨h0.1, h0.2, ?_⟩
    have hG : omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := right_ne_zero_of_mul hne
    unfold omegaG at hG
    unfold omegaQ at hQ
    split_ifs at hG with hg
    · split_ifs at hQ with hq
      · obtain ⟨a, ha1, ha2, ha3⟩ := hg.2
        refine ⟨?_, a, ha1, ha2, ha3⟩
        rintro PP (hP | hP)
        · rw [← ha1 ⟨PP, hP⟩]
          exact (a ⟨PP, hP⟩).isUnit.map Matrix.detMonoidHom
        · exact (hq PP hP).2
      · exact absurd rfl hQ
    · exact absurd rfl hG
  · exact absurd rfl hne

end GlobalTheory.FinZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalHeckeCharDetDoubleCosetSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetVal

open Formalism.L2.Host (IsUnitAt IsUnifAt)

theorem isUnitAt_det_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w n) :
    IsUnitAt w (Matrix.GeneralLinearGroup.det k) := by
  unfold GlobalTheory.LFun.KGL at hk
  obtain ⟨k', rfl⟩ := hk
  set c := Matrix.GeneralLinearGroup.det k' with hc
  have hdc : ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (Formalism.UG.Ov E w).subtype k') :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((c : Formalism.UG.Ov E w) : w.adicCompletion E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hc, Matrix.GeneralLinearGroup.val_det_apply]
    unfold Formalism.UG.bc
    rw [Units.coe_map]
    exact (RingHom.map_det _ _).symm
  have hle : ∀ y : Formalism.UG.Ov E w, Valued.v (y : w.adicCompletion E) ≤ 1 := fun y =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers ..).1 y.2
  have h3 : Valued.v ((c : Formalism.UG.Ov E w) : w.adicCompletion E) *
      Valued.v ((↑c⁻¹ : Formalism.UG.Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  unfold Formalism.L2.Host.IsUnitAt
  rw [hdc]
  refine le_antisymm (hle _) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hle _)

theorem locChar_det_doubleCoset : ∀ (D : D7) (T : HSp D) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), UnrAt χ w → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ((locChar χ w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)))) : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ (∑ i, d i) := by
  intro D T χ v w h hχ e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨⟨a, -, hea⟩, -⟩ := he
  have hloc : ∀ g, locMat D.sp.cm.sig T.gram h g = a * e g * a⁻¹ := fun g => by
    rw [hea g]
    group
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    unfold IsUnifV at hϖ
    simp at hϖ
  set u : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hu
  have hprod : ∀ s : Finset (Fin T.rank), ∏ i ∈ s, u ^ d i = u ^ ∑ i ∈ s, d i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, _root_.zpow_add]
  have hdt : Matrix.GeneralLinearGroup.det t = u ^ ∑ i, d i := by
    rw [← hprod]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ht, Matrix.det_diagonal, Units.coe_prod]
    simp only [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
  have hdet : Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂))) =
      Matrix.GeneralLinearGroup.det k₁ * u ^ (∑ i, d i) * Matrix.GeneralLinearGroup.det k₂ := by
    simp only [hloc, MulEquiv.apply_symm_apply, map_mul, map_inv, hdt]
    rw [mul_comm (Matrix.GeneralLinearGroup.det a), mul_inv_cancel_right]
  have hunif := hχ.locChar_eq_val (x := u) (by
    show Valued.v (u : w.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ)
    rw [hu, Units.val_mk0, hϖ]
    rfl)
  rw [hdet, map_mul, map_mul, hχ _ (isUnitAt_det_of_mem_KGL _ hk₁), hχ _ (isUnitAt_det_of_mem_KGL _ hk₂),
    one_mul, mul_one, map_zpow, hunif, Units.val_zpow_eq_zpow_val]

end GlobalTheory.DetVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatch
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompIdem

theorem projV_eq_of_idem : ∀ {D : D7} (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g k : GA D T) (ε : AE D), compFin D.host.F D.host.E v ε = 1 → Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → projV T v k = projV T v g := by
  intro D T v g k ε hε h
  apply GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig T.gram
  apply Units.ext
  show (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v k)).1 =
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v g)).1
  rw [GlobalTheory.AdelicU.matHom_proj, GlobalTheory.AdelicU.matHom_proj]
  show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram k).1).map (compFin D.host.F D.host.E v) =
    ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g).1).map (compFin D.host.F D.host.E v)
  change (Formalism.L2.Theta.mt T k).map _ = (Formalism.L2.Theta.mt T g).map _
  rw [h, GlobalTheory.CompStab.map_idem, hε, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.CompIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (H : Subgroup (GA D S × GA D T)), IsClosed (H : Set (GA D S × GA D T)) → (∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H) → ∀ g h, Stab S βS g → Stab T βT h → (g, h) ∈ H := by
  first | exact @GlobalTheory.StabDense.mem_of_local | exact GlobalTheory.StabDense.mem_of_local | (intros; apply GlobalTheory.StabDense.mem_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedLatticeReframeHomMatrixIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_reframeHomMatrix_iff : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T), u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔ reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := by
  first | exact @GlobalTheory.AdSpan.ReVec.latO_reW_iff | exact GlobalTheory.AdSpan.ReVec.latO_reW_iff | (intros; apply GlobalTheory.AdSpan.ReVec.latO_reW_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemLevRed

theorem mem_lev_of_reductions : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (y : GL (Fin T.rank) (EAf D)), LT.Q = ∅ → y ∈ UA D.sp.cm T.gram → y ∈ St βT → ∀ (a b : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1)), (∀ PP, a PP ∈ blockTri (blkOf LT.r LT.t)) → (∀ PP, b PP ∈ blockTri (blkOf LT.r LT.t)) → (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H → (fun PP => upperLeftBlock LT.hr (b PP)) ∈ LT.P.H → (∀ PP : ↥LT.Pg, b PP * redFn βT PP.1 y = a PP) → y ∈ lev D.sp.cm T.gram βT LT := by
  intro D T βT LT y hQ hU hS a b ha hb hHa hHb hab
  have hred : ∀ PP : ↥LT.Pg, redFn βT PP.1 y = (b PP)⁻¹ * a PP := fun PP => by
    rw [← hab PP, inv_mul_cancel_left]
  refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rw [hred ⟨PP, hP⟩]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hb ⟨PP, hP⟩)) (ha ⟨PP, hP⟩)
  · rw [hQ] at hP
    exact absurd hP (Finset.notMem_empty PP)
  · have h1 : rTup βT LT y = (fun PP => upperLeftBlock LT.hr (b PP)) ⁻¹ * (fun PP => upperLeftBlock LT.hr (a PP)) := by
      funext PP
      have hb2 := blockTri_blkOf_le LT.r LT.t (hb PP)
      have ha2 := blockTri_blkOf_le LT.r LT.t (ha PP)
      show upperLeftBlock LT.hr (redFn βT PP.1 y) = (upperLeftBlock LT.hr (b PP))⁻¹ * upperLeftBlock LT.hr (a PP)
      rw [hred PP]
      unfold upperLeftBlock
      rw [extendMatrixByIdentityAlongIndices_mul _ (Subgroup.inv_mem _ hb2) ha2, extendOne_inv _ hb2]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hHb) hHa

end GlobalTheory.MemLevRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairActionStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelInvariantForm_upperTriangular_pair_action : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  first | exact @GlobalTheory.SphTheta.mixLat_form_borel | exact GlobalTheory.SphTheta.mixLat_form_borel | (intros; apply GlobalTheory.SphTheta.mixLat_form_borel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecSubMemLatticeCompletionOfLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulVec_sub_mem_latticeCompletion_of_lattice : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)), (∀ x ∈ L, m *ᵥ toAf x - toAf x ∈ hatV L') → ∀ u ∈ hatV L, m *ᵥ u - u ∈ hatV L' := by
  first | exact @GlobalTheory.LevExt.mulVec_sub_mem_hatV | exact GlobalTheory.LevExt.mulVec_sub_mem_hatV | (intros; apply GlobalTheory.LevExt.mulVec_sub_mem_hatV <;> assumption)
end

