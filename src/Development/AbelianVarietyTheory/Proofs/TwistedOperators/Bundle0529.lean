import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulHalfOrthogonalIdempotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfSplit

def kIdx (k : ℕ) (A : Type) [AddCommGroup A] : ℕ := (nsmulAddMonoidHom k : A →+ A).range.index

theorem relIndex_eq_kIdx {G : Type} [AddCommGroup G] (H : AddSubgroup G) (k : ℕ) :
    (AddSubgroup.map (nsmulAddMonoidHom k) H).relIndex H = kIdx k H := by
  unfold kIdx AddSubgroup.relIndex
  congr 1
  ext x
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyx)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩

theorem kIdx_congr {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (k : ℕ) :
    kIdx k A = kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_map_equiv _ e]
  congr 1
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨k • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩

theorem kIdx_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] (k : ℕ) :
    kIdx k (A × B) = kIdx k A * kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_prod]
  congr 1
  ext ⟨a, b⟩
  simp only [AddSubgroup.mem_prod, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨⟨x, y⟩, hxy⟩
    exact ⟨⟨x, congrArg Prod.fst hxy⟩, ⟨y, congrArg Prod.snd hxy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨(x, y), Prod.ext hx hy⟩

theorem kIdx_subsingleton {A : Type} [AddCommGroup A] [Subsingleton A] (k : ℕ) : kIdx k A = 1 :=
  AddSubgroup.index_eq_one.2 (eq_top_iff.2 fun x _ => ⟨0, Subsingleton.elim _ _⟩)

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

section split

variable (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M) {e f : R}

include hmem in
theorem smul_mem_inf (he : e * e = e) (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) {u : M} (hu : u ∈ Λ) : e • u ∈ Λ ⊓ h e :=
  AddSubgroup.mem_inf.2 ⟨hΛe u hu, (hmem _ _).2 (by rw [smul_smul, he])⟩

def splitEquiv (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) (hΛf : ∀ u ∈ Λ, f • u ∈ Λ) :
    ↥(Λ ⊓ h (e + f)) ≃+ ↥(Λ ⊓ h e) × ↥(Λ ⊓ h f) where
  toFun u := (⟨e • u.1, smul_mem_inf h hmem Λ he hΛe (AddSubgroup.mem_inf.1 u.2).1⟩,
    ⟨f • u.1, smul_mem_inf h hmem Λ hf hΛf (AddSubgroup.mem_inf.1 u.2).1⟩)
  invFun p := ⟨p.1.1 + p.2.1, AddSubgroup.mem_inf.2 ⟨add_mem (AddSubgroup.mem_inf.1 p.1.2).1
      (AddSubgroup.mem_inf.1 p.2.2).1, (hmem _ _).2 (by
        have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
        have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
        have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
        have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
        rw [smul_add, add_smul, add_smul, h1, h2, h3, h4, add_zero, zero_add])⟩⟩
  left_inv u := by
    apply Subtype.ext
    change e • (u : M) + f • (u : M) = u
    rw [← add_smul]
    exact (hmem _ _).1 (AddSubgroup.mem_inf.1 u.2).2
  right_inv p := by
    have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
    have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
    have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
    have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((p.1 : M) + p.2) = p.1
      rw [smul_add, h1, h4, add_zero]
    · change f • ((p.1 : M) + p.2) = p.2
      rw [smul_add, h2, h3, zero_add]
  map_add' u v := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((u : M) + v) = e • (u : M) + e • (v : M)
      exact smul_add _ _ _
    · change f • ((u : M) + v) = f • (u : M) + f • (v : M)
      exact smul_add _ _ _

end split

theorem sum_idem {ι : Type} (s : Finset ι) (cs : ι → R) (hid : ∀ i ∈ s, cs i * cs i = cs i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) :
    (∑ i ∈ s, cs i) * (∑ i ∈ s, cs i) = ∑ i ∈ s, cs i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji)) (fun h => absurd hi h), hid i hi]

theorem kIdx_half_sum (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M)
    {ι : Type} (P : Finset ι) (cs : ι → R) (hid : ∀ i ∈ P, cs i * cs i = cs i)
    (horth : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) (hΛ : ∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) (k : ℕ) :
    kIdx k ↥(Λ ⊓ h (∑ i ∈ P, cs i)) = ∏ i ∈ P, kIdx k ↥(Λ ⊓ h (cs i)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    haveI : Subsingleton ↥(Λ ⊓ h 0) := ⟨fun a b => by
      have ha := (hmem _ _).1 (AddSubgroup.mem_inf.1 a.2).2
      have hb := (hmem _ _).1 (AddSubgroup.mem_inf.1 b.2).2
      rw [zero_smul] at ha hb
      exact Subtype.ext (ha.symm.trans hb)⟩
    exact kIdx_subsingleton k
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hne : ∀ j ∈ s, a ≠ j := fun j hj haj => ha (haj ▸ hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj))
        (fun i hi => hΛ i (hs i hi)),
      kIdx_congr (splitEquiv h hmem Λ (hid a ha')
        (sum_idem s cs (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj)))
        (by rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun j hj => horth a ha' j (hs j hj) (hne j hj))
        (by rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun j hj => horth j (hs j hj) a ha' (hne j hj).symm)
        (hΛ a ha')
        (fun u hu => by rw [Finset.sum_smul]; exact AddSubgroup.sum_mem _ fun i hi => hΛ i (hs i hi) u hu)),
      kIdx_prod]

theorem relIndex_nsmul_half_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  intro D S T Λ ι P cs hid horth hΛ k
  rw [relIndex_eq_kIdx]
  simp only [relIndex_eq_kIdx]
  exact kIdx_half_sum (GlobalTheory.PlaceModel.half S T) (fun e u => GlobalTheory.PlaceModel.mem_half S T) Λ P cs hid horth hΛ k

end GlobalTheory.HalfSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.HalfIndex

theorem relIndex_nsmul_half : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT c v π hc hπ k hk
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  obtain ⟨σ, q1, q2⟩ := GlobalTheory.SplitLinear.exists_section (S := S) (T := T) hc.1 hπ
  have inj : Function.Injective σ := fun w w' h => by rw [← q1 w, h, q1]
  have hinf : infPart D c = 0 := GlobalTheory.PlaceModelSum.infPart_split hc
  set L0 := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hL0
  set L := L0.comap σ with hL
  have hM : L0 ⊓ GlobalTheory.PlaceModel.half S T c = L.map σ := by
    rw [hL, AddSubgroup.map_comap_eq, ← GlobalTheory.SplitLinear.section_range hπ q1 q2, inf_comm]
  let nk : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    nsmulAddMonoidHom k
  have hcomm : (L.map σ).map (nsmulAddMonoidHom k) = (L.map nk).map σ := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun w => (map_nsmul σ k w).symm
  have e1 : ((L0 ⊓ GlobalTheory.PlaceModel.half S T c).map (nsmulAddMonoidHom k)).relIndex (L0 ⊓ GlobalTheory.PlaceModel.half S T c) =
      (L.map nk).relIndex L := by
    rw [hM, hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ inj]
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hnk : ∀ w, nk w = (k : Fv D.host.F v) • w := fun w => (Nat.cast_smul_eq_nsmul (Fv D.host.F v) k w).symm
  have nkinj : Function.Injective nk := fun w w' h => by
    rw [hnk, hnk] at h
    exact smul_right_injective _ hk0 h
  have nksurj : Function.Surjective nk := fun w => ⟨(k : Fv D.host.F v)⁻¹ • w, by rw [hnk, smul_inv_smul₀ hk0]⟩
  have e2 : (L.map nk).relIndex L = L.relIndex (L.comap nk) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective L (L.comap nk) nkinj,
      AddSubgroup.map_comap_eq_self_of_surjective nksurj]
  let u : (Fv D.host.F v)ˣ := Units.mk0 _ hk0
  have hH : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v),
      ((k : Fv D.host.F v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v))) * w * (1 : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v)) = nk w := fun w => by
    rw [hnk, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hA := GlobalTheory.SplitLinear.relIndex_matrix_lattice D.host.F v S.rank T.rank L (L.comap nk)
    (fun o ho m hm => GlobalTheory.SplitLinear.section_smul hc.1 hπ q1 q2 o ho m hm)
    (GlobalTheory.SplitLinear.section_den hS hT hπ q1 q2) (fun w => ?_)
    ((k : Fv D.host.F v) • 1) 1 1 (u ^ T.rank) (by simp) (by simp [u, Matrix.det_smul]) (fun m hm => ?_) (fun w => ?_)
  rotate_left
  · obtain ⟨N, hN, h1⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS hT (σ w)
      (GlobalTheory.PlaceDatum.infPart_of_half hinf (q2 w))
    exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, map_nsmul]⟩
  · rw [hH]
    exact nsmul_mem hm k
  · rw [hH]
    rfl
  have hkc : (((k : v.adicCompletionIntegers D.host.F)) : Fv D.host.F v) = (k : Fv D.host.F v) := by simp
  have hv : Valued.v (k : Fv D.host.F v) ≠ 0 := by simpa using hk0
  have h1 : Valued.v (k : Fv D.host.F v) ≤ 1 := hkc ▸ (k : v.adicCompletionIntegers D.host.F).2
  have hl : WithZero.log (Valued.v (k : Fv D.host.F v)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hv, WithZero.exp_zero]; exact h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (Valued.v (k : Fv D.host.F v)) = -(e : ℤ) :=
    ⟨(-WithZero.log (Valued.v (k : Fv D.host.F v))).toNat, by omega⟩
  have he' : Valued.v (k : Fv D.host.F v) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, WithZero.exp_log hv]
  have hcard := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers D.host.F v).2
    (k : v.adicCompletionIntegers D.host.F) e (by rw [hkc]; exact he')
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v u = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ e)⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, Units.val_mk0, he, zpow_neg, zpow_natCast]
  have h1' : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  rw [e1, e2, hcard]
  apply Nat.cast_injective (R := ℝ)
  rw [hA, GlobalTheory.SplitLinear.absV_pow, hu, h1']
  push_cast
  rw [one_pow, one_mul, ← pow_mul, inv_pow, inv_inv, mul_comm T.rank S.rank]

end GlobalTheory.HalfIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainSteps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

namespace WeakSepPf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

variable (G) in

theorem nonempty_coreVol : Nonempty (CoreVol G) := ⟨fun i => (GlobalTheory.Unf.Inhab.nonempty_vol (G.V (.core i))).some⟩

theorem rapidDec_of_rapidRow {M : Vol G} {u : GA D (Yc D 0) → ℂ} (h : RapidRow W M u) : RapidDec (Yc D 0) u :=
  h (fun _ => 0) (fun _ => default) 0 (Nat.zero_le _)

theorem rapidDec_of_reach {v : CoreVol G} {F : Fn G (.core 0)} (h : F ∈ Reach W v) : RapidDec (G.V (.core 0)) F := by
  obtain ⟨Ψ, hΨ, rfl, -⟩ := h
  exact hΨ.1 0 (Nat.zero_le _)

theorem integrableOn_corePeriod_rapidlyDecreasing {M : Vol G} (hM : M.IsRow) {F : Fn G (.core 0)}
    (hF : RapidDec (G.V (.core 0)) F) {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) :
    IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) := by
  obtain ⟨h1, h2⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨C, hC⟩ := hF.2.2 0
  exact RapidDec.integrableOn_mul_of_le (V := Yc D 0) (f := fun h => F (stabilizerEmbedding G.sp.dec0 h)) hu h1 h2
    ((hF.2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding G.sp.dec0)).aestronglyMeasurable) (C := C) (A := 0)
    fun g => by simpa using hC _

theorem exists_reach_of_span {M : Vol G} (hM : M.IsRow) {v : CoreVol G}
    {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) {F : Fn G (.core 0)} (hF : F ∈ Submodule.span ℂ (Reach W v))
    (h0 : per0 G M F u ≠ 0) : ∃ F' ∈ Reach W v, per0 G M F' u ≠ 0 := by
  by_contra hn
  push_neg at hn
  have key : IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) ∧
      per0 G M F u = 0 := by
    clear h0
    induction hF using Submodule.span_induction with
    | mem x hx => exact ⟨integrableOn_corePeriod_rapidlyDecreasing hM (rapidDec_of_reach W hx) hu, hn x hx⟩
    | zero => exact ⟨by simp only [Pi.zero_apply, zero_mul]; exact integrableOn_zero, by simp [per0]⟩
    | add x y _ _ hx hy =>
      have e : (fun h => (x + y) (stabilizerEmbedding G.sp.dec0 h) * u h) =
          fun h => x (stabilizerEmbedding G.sp.dec0 h) * u h + y (stabilizerEmbedding G.sp.dec0 h) * u h := by
        funext h; simp [add_mul]
      refine ⟨e ▸ hx.1.add hy.1, ?_⟩
      have a := hx.2
      have b := hy.2
      unfold per0 at a b ⊢
      erw [e, integral_add hx.1 hy.1, a, b, add_zero]
    | smul c x _ hx =>
      have e : (fun h => (c • x) (stabilizerEmbedding G.sp.dec0 h) * u h) = fun h => c * (x (stabilizerEmbedding G.sp.dec0 h) * u h) := by
        funext h; simp [mul_assoc]
      refine ⟨e ▸ hx.1.const_mul c, ?_⟩
      have a := hx.2
      unfold per0 at a ⊢
      erw [e, integral_const_mul, a, mul_zero]
  exact h0 key.2

end WeakSepPf

theorem weakSep_of_steps : SizeGap → CoreModels → RowRapid → PeriodNe → CoreOnto → Ascent → WeakSep := by
  intro hs h1 h2 h3 h4 h5 ε CF hCF
  obtain ⟨x, hx⟩ := h3 ε CF hCF
  obtain ⟨x', hx'⟩ := hs ε
  refine ⟨max x x', fun D large₂ e a b T L μ0 hL G W M hM M₀ hc0 t ht t0 w w0 => ?_⟩
  have q := offQ_of_sizeRows b
  have s := hx' D large₂ e (le_trans (le_max_right _ _) a) b
  obtain ⟨MP, hMP⟩ := h1 D q T L μ0 hL _ G W M hM 0 (Nat.zero_le _)
  obtain ⟨y, hy, v, hv, hp⟩ := hx D large₂ e (le_trans (le_max_left _ _) a) b T L μ0 hL G W M hM M₀ MP t ht t0 w w0
  obtain ⟨vol⟩ := WeakSepPf.nonempty_coreVol G
  have hr := (h2 D q s T L μ0 hL _ rfl G W M hM M₀ hc0 t ht w).1
  obtain ⟨F, ⟨Ψ, hΨ, rfl, c, hcol, ξ, hξ⟩, hF⟩ := WeakSepPf.exists_reach_of_span W hM (WeakSepPf.rapidDec_of_rapidRow W hr)
    (h4 D q s T L μ0 hL _ rfl G W M hM vol MP hMP y hy v hv) hp
  obtain ⟨ρ, Φ, hB⟩ := h5 D q T L μ0 hL _ G W M hM vol Ψ hΨ _ hr hF
  exact ⟨ρ, ξ, c, hcol, Φ, by rw [fPsiPhi, ← hξ]; exact hB⟩

end GlobalTheory.SepRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

def thSub (W : G.Weil) (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {f | IsThetaFunO W.ψ (G.pS p) (G.pT p) f}
  add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg

open Classical in

def toTh (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : thSub W p :=
  if h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f then ⟨f, h⟩ else 0

theorem coe_toTh (W : G.Weil) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) :
    (toTh W p f : WO (G.pS p) (G.pT p) → ℂ) = f := by
  simp [toTh, h]

def lastIx (D : D7) : Fin D.R.m := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩

theorem lastIx_succ (D : D7) : D.R.m = (lastIx D : ℕ) + 1 := by
  have := D.R.two_le_m
  simp only [lastIx]
  omega

variable {W : G.Weil}

def colMapV (S : GridChoice W U) {t : T} (fs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (fs ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (gs ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

theorem colMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (x : ∀ j, FinPt G (.top j)) :
    S.colMap d x = colMapV S (fun j => S.Z.vec (d.1 j)) x := rfl

theorem rowMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    S.rowMap d y = rowMapV S (fun i => S.Z.vec (d.2 i)) y := rfl

def topLast (g : FinPt G (.top D.R.m)) : FinPt G (.top ((lastIx D : ℕ) + 1)) := lastIx_succ D ▸ g

def gridLast (g : FinPt G (.grid D.R.m D.R.m)) : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m) := lastIx_succ D ▸ g

def colShift (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) :=
  W.om (.top t (lastIx D)) (G.toPair (.top t (lastIx D)) 1
    (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1)

def rowShift (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (lastIx D) D.R.m) (G.toPair (.chi (lastIx D) D.R.m) 1
    (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1)

end GlobalTheory.LastVertexInv

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inRange_top (t : T) (j : Fin D.R.m) : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := by
  have := j.2
  simp [Pair.InRange, Node.InRange]

theorem inRange_chi (i : Fin D.R.m) : (Pair.chi (i : ℕ) D.R.m : Pair T).InRange D.R.m := by
  have := i.2
  simp [Pair.InRange, Node.InRange]

theorem defPair_top (t : T) (j : Fin D.R.m) : DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) := by
  have := j.2
  simp [DefPair]

theorem defPair_chi (i : Fin D.R.m) : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := by
  have := i.2
  simp [DefPair]

theorem vec_theta (S : GridChoice W U) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (hIn : p.InRange D.R.m)
    (d : FinDatum G t p) (h : S.Z.HasVec d) : IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (S.Z.vac_is p hp).2.theta)

theorem colShift_theta (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    {f : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (colShift S t g f) :=
  (W.om_is _ (inRange_top t (lastIx D))).om_pres _ _ h

theorem rowShift_theta (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m))
    {f : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (rowShift S k f) :=
  (W.om_is _ (inRange_chi (lastIx D))).om_pres _ _ h

end GlobalTheory.LastVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerDerivRelationOfHeisenbergDerivStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  first | exact @GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv | exact GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv | (intros; apply GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv <;> assumption)
end

