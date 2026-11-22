import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0598
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0698
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0704
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0700
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0699

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMoved
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColVac

variable {D : D7} {T : Type}

theorem xi_mem_xiVals {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (x : (AE D)ˣ) :
    Circle.toUnits (L.xi t x) ∈ xiVals L t := by
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e : L.xi t x = L.xi t (b x) := by
    conv_lhs => rw [hab x, map_mul, GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (ha x).2, one_mul]
  rw [e]
  have hx := (hb x).1
  generalize b x = u at hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 _ _ (hL.xi t)
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (u : AE D)), ι (finPart D ((u⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod u hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  have h6 : Circle.toUnits (L.xi t u) = ∏ P ∈ S, (L.xiH t).locK P (k P) := by
    apply Units.ext
    rw [Units.coe_prod]
    exact h5
  rw [h6]
  exact prod_mem fun P _ => Subgroup.subset_closure ⟨P, _, rfl⟩

theorem attChr_mu {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (j n : ℕ) :
    Formalism.IndefR.Lift.attChr (L.mu t j) L.eta n = Formalism.IndefR.Lift.attChr (L.mu μ0 j) L.eta n * L.xi t := by
  have hb : L.xi μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ0))
  have e : L.mu t j = L.mu μ0 j * L.xi t := by
    show L.mu0 j * L.xi t = L.mu0 j * L.xi μ0 * L.xi t
    rw [hb, mul_one]
  unfold Formalism.IndefR.Lift.attChr
  rw [e]
  split_ifs
  · exact mul_right_comm _ _ _
  · rfl

section Move

variable {V : HSp D} {k : GA D V} {C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

set_option synthInstance.maxHeartbeats 400000 in

theorem fwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (h _).1 (Submodule.subset_span ⟨s, hs, rfl⟩)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  have e2 : (Formalism.IndefR.Lev.finE V k).1 * (Formalism.IndefR.Lev.finE V k⁻¹).1 = 1 :=
    congrArg Units.val (((Formalism.IndefR.Lev.finE V).map_mul k k⁻¹).symm.trans
      ((congrArg (Formalism.IndefR.Lev.finE V) (mul_inv_cancel k)).trans (Formalism.IndefR.Lev.finE V).map_one))
  rw [GlobalTheory.MovedHomLat.bridge]
  refine (h _).2 ?_
  rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨s, hs, rfl⟩

end Move

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U}

theorem isVac_moved (Z : Normal W N) (t : T) {j : ℕ} (hj : j < D.R.m) :
    W.IsVac (.top t j) (W.om (.top t j) ((N.u (.top j)).1, (N.u (.top (j + 1))).1) (Z.vac (.top t j))) := by
  have h0 := N.u_lat (.top j) hj.le
  have h1 := N.u_lat (.top (j + 1)) hj
  have H := GlobalTheory.MovedHomLat.actO_latO_onto (G.V (.top j)) (G.V (.top (j + 1))) (N.u (.top j)).1 (N.u (.top (j + 1))).1
    _ _ _ _ (fwd h0) (fwd h1) (bwd h0) (bwd h1)
  refine GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)) W.θ_is
    _ _ _ _ _ _ _ _ _ _ (fun τ => ?_) (fun τ => ?_) (fun u => ⟨fun hu => ?_, ?_⟩) _ (Z.vac_is (.top t j) hj)
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top j)).2, Matrix.mul_one, Matrix.one_mul]
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top (j + 1))).2, Matrix.mul_one, Matrix.one_mul]
  · obtain ⟨w, hw, e⟩ := H.2 u hu
    exact ⟨w, hw, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact H.1 w hw

theorem colVac : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch _
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  choose x hx using fun j => GlobalTheory.RecDict.exists_isDetRoot D (ch.G.V (.top j)) (ch.S.N.u (.top j)).1
  refine ⟨fun j => ch.W.om (.top A.μ0 j) ((ch.S.N.u (.top j)).1, (ch.S.N.u (.top (j + 1))).1) (ch.S.Z.vac (.top A.μ0 j)),
    fun t j hj => isVac_moved ch.S.Z A.μ0 hj, fun _ => 1,
    fun t j => Circle.toUnits (R.toLevCh.xi t ((x j)⁻¹ * x (j + 1))),
    fun t j => xi_mem_xiVals hL t _, fun t j hj => ?_⟩
  have hW0 := ch.W.om_is (.top A.μ0 j) (show j + 1 ≤ D.R.m from hj)
  have hWt := ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have eS : ch.G.chrS (.top t j) = ch.G.chrS (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  have eT : ch.G.chrT (.top t j) = ch.G.chrT (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  rw [eS, eT] at hWt
  have e := GlobalTheory.TupRoot.twist_eq hW0 hWt (hx j) (hx (j + 1)) (ch.S.Z.vac_is (.top A.μ0 j) hj).2.theta
  rw [(ch.S.Z.free t A.μ0 j).2.1]
  refine e.trans ?_
  congr 1
  rw [one_mul, ← MonoidHom.map_inv, ← MonoidHom.map_mul]
  rfl

end GlobalTheory.ColVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportUnitaryPointReplacesPureTensorFactoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (gS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J),
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ v ∉ S, φ' v = φ v) ∧
        (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
        om (gS, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  first | exact @GlobalTheory.PlaceProd.pure_of_finSupp | exact GlobalTheory.PlaceProd.pure_of_finSupp | (intros; apply GlobalTheory.PlaceProd.pure_of_finSupp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

theorem dblP_big : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hChr hArr hLoc hBes hJac
  intro t w hw p hp β r r₀ h hpts M hM φ v f hvf j hje hj
  have hstd : IsStdChar D ch.W.ψ (-1) := by rw [hch.weil.ψ]; exact s.std
  obtain ⟨hψ, hcond, -⟩ := hChr t w hw p hp
  have hm := D.R.m_even
  have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨a, ha⟩ := hm; obtain ⟨b, hb⟩ := hje; omega
  have hj2 : j + 1 + 1 + 2 * ((D.R.m - 4 - j) / 2) + 2 = D.R.m := by omega
  have h0 : ¬ j + 2 * 0 + 2 = D.R.m := by omega
  have hL := hLoc t w hw p hp β r r₀ h hpts
  have t0 : topRank (locGrid ch.G t w) j + D.R.m = (locGrid ch.G t w).rank (D.R.m, j) + j + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have t1 : topRank (locGrid ch.G t w) (j + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1) + (j + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have t2 : topRank (locGrid ch.G t w) (j + 1 + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) + (j + 1 + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hc0 : topRank (locGrid ch.G t w) j + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by
    omega
  have hc1 : topRank (locGrid ch.G t w) (j + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1) := by
    omega
  have hc2 : topRank (locGrid ch.G t w) (j + 1 + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) := by
    omega
  have hodd : Odd (j + 1) := hje.add_one
  have hev2 : Even (j + 1 + 1) := hodd.add_one

  obtain ⟨T₁, hT₁, hO₁, Φ₁, hΦ₁, hTΦ₁⟩ := hArr t w hw p hp φ j (by omega) (v ⟨j, by omega⟩) (f ⟨j, by omega⟩)
    (hvf ⟨j, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h j * r₀ j) ((r₀ j)⁻¹ * r j) (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1))
    (hL j (by omega)).1 (hL (j + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1)) (frame hc0) (frame hc1)
  obtain ⟨T₂, hT₂, hO₂, Φ₂, hΦ₂, hTΦ₂⟩ := hArr t w hw p hp φ (j + 1) (by omega) (v ⟨j + 1, by omega⟩) (f ⟨j + 1, by omega⟩)
    (hvf ⟨j + 1, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1)) (h (j + 1 + 1) * r₀ (j + 1 + 1))
    ((r₀ (j + 1 + 1))⁻¹ * r (j + 1 + 1))
    (hL (j + 1) (by omega)).1 (hL (j + 1 + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1)) (frame hc1) (frame hc2)

  have hB0 := hBes t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h j * r₀ j) ((hL j (by omega)).2.1 hje) _ hc0
  have hJ1 := hJac t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1) * r₀ (j + 1)) (Or.inr ((hL (j + 1) (by omega)).2.2 hodd)) _ hc1
  have hB2 := hBes t w hw p hp M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1 + 1) * r₀ (j + 1 + 1)) ((hL (j + 1 + 1) (by omega)).2.1 hev2) _ hc2
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  have hxi := Witness.xi_ne p
  have es : (p.xi ^ ((D.R.m - 4 - j) / 2 + 1))⁻¹ * p.xi = (p.xi ^ ((D.R.m - 4 - j) / 2))⁻¹ := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hxi, mul_one]
  let Fd : GlobalTheory.LocMod.Dbl p (besAt ch.G hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) (j + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1 + 1))) (2 * ((D.R.m - 4 - j) / 2)) :=
    ⟨_, inv_ne_zero (pow_ne_zero _ hxi), _, _, _, _, _, _, hB0, hJ1, es ▸ hB2⟩

  obtain ⟨O₁, hOne₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
  obtain ⟨O₂, hOne₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
  have hv1 : ch.W.om (.mu t D.R.m j) ((h * r₀) j, (h * r₀) (j + 1)) (v ⟨j, by omega⟩) = T₁ O₁ := (hO₁ O₁ hOne₁).symm
  have hv2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r₀) (j + 1), (h * r₀) (j + 1 + 1)) (v ⟨j + 1, by omega⟩) = T₂ O₂ :=
    (hO₂ O₂ hOne₂).symm
  have hf1 : ch.W.om (.mu t D.R.m j) ((h * r) j, (h * r) (j + 1)) (f ⟨j, by omega⟩) = T₁ Φ₁ := by
    rw [hTΦ₁]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have hf2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r) (j + 1), (h * r) (j + 1 + 1)) (f ⟨j + 1, by omega⟩) = T₂ Φ₂ := by
    rw [hTΦ₂]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have E : ∀ (Φ : SchDown ch.G t) (g : Pts ch.G), conAt ch.W hM Φ g j =
      GlobalTheory.Unf.contr (linkAt hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (GlobalTheory.Unf.flatBF (B := besAt ch.G hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ hj')
            (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega)))
          (ch.W.om (.mu t D.R.m j) (g j, g (j + 1)) (Φ ⟨j, by omega⟩)))
        (GlobalTheory.Unf.flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (stepAt ch.G ch.W t hM (j + 1) (by omega) (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
            (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega)))
          (ch.W.om (.mu t D.R.m (j + 1)) (g (j + 1), g (j + 1 + 1)) (Φ ⟨j + 1, by omega⟩))) := by
    intro Φ g
    unfold conAt
    rw [dif_neg h0]
    exact dif_pos hj'
  rw [E v (h * r₀), E f (h * r)]
  rw [hv1, hv2, hf1, hf2]
  have hz : ∀ (S' : Finset I), (∀ q₁ q₂, ∑ i ∈ S', x i * ((Ξ₁ i).1 q₁ * (Ξ₂ i).1 q₂) = 0) → ∀ q,
      GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w) (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1)
        (0 : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
          (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1)) (Kw w))).1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S', x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
    intro S' hS' q
    rw [hS' q.1 q.2]
    simp [GlobalTheory.LocFlat.contr, GlobalTheory.LocFlat.flCol, GlobalTheory.RootEx.opE, GlobalTheory.StepData.hat]
  refine ⟨fun hvan => ?_, fun hq => ?_⟩
  · refine Eq.trans (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond
      ((D.R.m - 4 - j) / 2) _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc (hz S hvan)).symm ?_
    exact (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I ∅ x Ξ₁ Ξ₂ c₁ c₂ (by simp)
      (hz ∅ fun _ _ => Finset.sum_empty)).trans Finset.sum_empty
  · have hloc : ∀ q, GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w)
        (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1) Φ₁.1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
      intro q
      rw [← hq q, show Φ₁.1 = _ from funext hΦ₁, show Φ₂.1 = _ from funext hΦ₂]
      unfold facAt locA
      rw [dif_neg (show ¬ j + 2 * 0 + 2 = (locGrid ch.G t w).m from h0),
        dif_pos (show j + 2 * (((locGrid ch.G t w).m - 4 - j) / 2 + 1) + 2 = (locGrid ch.G t w).m from hj')]
      rfl
    exact GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hloc

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryLastTwoStepsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.LastPlace

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

open ValuativeRel in

theorem combAt_renumber {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T' : HSp D} {Y Y' Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] [Fintype Z] [DecidableEq Z] (FS : Frame k S.rank Y') (F : Frame k T'.rank Y) (FX : Frame k T'.rank Z)
    (e : Z ≃ Y) (he : ∀ r z, FX.β r z = F.β r (e z)) (c : WO S T' →₀ ℂ) (Ξ : Matrix Y Y' k → ℂ) :
    p.IsCombAt ψ FS F c Ξ → p.IsCombAt ψ FS FX c (fun x => Ξ (x.submatrix e.symm id)) := by
  rintro ⟨hsupp, hc⟩
  refine ⟨hsupp, fun Tm hTm Φ₀ Φ hΦ₀ hΦ => ?_⟩
  haveI : T2Space (Matrix Y Y' k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  have hc1 : Continuous fun y : Matrix Y Y' k => y.submatrix e id :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e a))
  have hc2 : Continuous fun x : Matrix Z Y' k => x.submatrix e.symm id :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e.symm a))
  let re : SB (Matrix Z Y' k) → SB (Matrix Y Y' k) := fun Ψ =>
    ⟨fun y => Ψ.1 (y.submatrix e id), GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 (fun y => by ext a b; simp)⟩
  obtain ⟨Tm', hTm', hchg⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k p Z Y' S T' FS FX Y Y' FS F ψ Tm hTm
  have hP : F.γ * FX.β = (F.γ * F.β).submatrix id e := by
    ext y z
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, he]
  have hre : ∀ (Ψ : SB (Matrix Z Y' k)), Tm' (re Ψ) = Tm Ψ := fun Ψ => hchg Ψ (re Ψ) fun x => by
    change Ψ.1 x = Ψ.1 ((F.γ * FX.β * x * (FS.γ * FS.β)).submatrix e id)
    have hx : (F.γ * FX.β * x * (FS.γ * FS.β)).submatrix e id = x := by
      rw [hP, F.γβ, FS.γβ, Matrix.mul_one]
      funext a b
      simp [Matrix.mul_apply, Matrix.one_apply]
    rw [hx]
  have h1 : IsOne (re Φ₀) := by
    unfold IsOne
    funext y
    change Φ₀.1 (y.submatrix e id) = _
    rw [hΦ₀]
    by_cases hy : ∀ r q, y r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (show y ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hy), Set.indicator_of_mem (show y.submatrix e id ∈ {x : Matrix Z Y' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun r q => hy (e r) q)]
    · rw [Set.indicator_of_notMem (show y ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hy), Set.indicator_of_notMem (show y.submatrix e id ∉ {x : Matrix Z Y' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun h => hy fun r q => by simpa using h (e.symm r) q)]
  have h2 : (re Φ).1 = Ξ := by
    funext y
    change Φ.1 (y.submatrix e id) = Ξ y
    rw [hΦ]
    simp
  rw [← hre Φ, ← hre Φ₀]
  exact hc Tm' hTm' (re Φ₀) (re Φ) h1 h2

end GlobalTheory.LastPlace

open GlobalTheory.LastPlace in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.FlatPlace.lastStep_eventually : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → LastP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  classical
  intro hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f hvf j hj
  have hj0 : j + 2 * 0 + 2 = D.R.m := by omega
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  have hA1 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have hA0 := topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have hA2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hAm := topRank_add (G := locGrid ch.G t w) one_le_sLen D.R.m
  rw [hm] at hA1 hA0 hA2 hAm
  have h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1) := by omega
  have h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by omega
  have h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m) := by
    rw [show j + 1 + 1 = D.R.m by omega]
  have h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1) := by omega
  obtain ⟨hchar, hcond, -⟩ := hChr t w hw p hp
  obtain ⟨F₀, T₁, hcore, hT₁, hT₁O, Φ₁, hΦ₁, hT₁Φ⟩ := GlobalTheory.T.lastTwoSteps_localModel_flatMap_fourierJacobiStep ch hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f
    hvf j hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some h₁ h₂
  obtain ⟨T₂, hT₂, hT₂O, Φ₂, hΦ₂, hT₂Φ⟩ := GlobalTheory.T.lastTwoSteps_localModel_extendByZero_topStep ch hChr hArr hJac t w hw p hp β M hM φ v f hvf j hj0 h₃ h₄
  obtain ⟨e, he1, he2, FX, hFX, hFXe⟩ := GlobalTheory.T.lastTwoSteps_topVertex_frame_at_place ch t w hw p hp j hj
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  haveI : T2Space (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  let Ξ₂' : I → SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    fun i => ⟨fun y => (Ξ₂ i).1 (y.submatrix e.symm id),
      GlobalTheory.FinPl.Comm.comp_mem_SB (Ξ₂ i).2 (p := fun y => y.submatrix e.symm id) (s := fun y => y.submatrix e id)
        (continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e.symm a)))
        (continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e a)))
        (fun y => by ext a b; simp)⟩
  have hΞ₂' : ∀ i y, (Ξ₂' i).1 y = (Ξ₂ i).1 (y.submatrix e.symm id) := fun _ _ => rfl
  let O₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) :=
    ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  let O₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  have hO₁ : IsOne O₁ := rfl
  have hO₂ : IsOne O₂ := rfl
  have hL : (pLine D).rank = 1 := rfl
  have ha : ((p.xi ^ 0)⁻¹ : Kw w) ≠ 0 := by simp
  have hz : (lastTau (D := D)).map p.pr *ᵥ (fun _ => (1 : Kw w)) =
      (-(p.xi * (p.xi ^ 0)⁻¹)) • fun i => p.pr ((besAt ch.G hM j 0 hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).ζ i) := by
    funext i
    simp [lastTau, mulVec, dotProduct, besAt, Place.xi, Place.pr, hL]
    exact (mul_one _).symm
  have key := fun (S' : Finset I) (Ψ₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w))) =>
    GlobalTheory.LastSeeSawGen.lastBi_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ ch.W.ψ_std (psiAt ch.W w) hchar hcond 0
      (besAt ch.G hM j 0 hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (ch.G.V (.top (j + 1))) (ch.G.V (.top (j + 1 + 1)))
      (ch.G.V (.grid D.R.m D.R.m)) (pLine D) (topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)) lastTau hL
      GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram ((p.xi ^ 0)⁻¹) (fun _ => 1) ha hz _ _ _ (frTop ch.S.toGridChoice t w j (by omega)) F₀
      (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) FX hcore hFX T₁ T₂ hT₁ hT₂ Φ₁ Ψ₂ O₁ O₂
      hO₁ hO₂ I S' x Ξ₁ Ξ₂' c₁ c₂
  have hc' : ∀ i ∈ S, p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j (by omega)) (frTop ch.S.toGridChoice t w (j + 1) (by omega))
      (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) FX (c₂ i) (Ξ₂' i).1 :=
    fun i hi => ⟨(hc i hi).1, combAt_renumber p ch.W.ψ _ _ FX e hFXe _ _ (hc i hi).2⟩
  have hsymm : ∀ a : Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)),
      e.symm (Fin.castLE (by omega) a) = Sum.inl (Fin.cast h₃ a) := fun a => by
    rw [Equiv.symm_apply_eq]; ext; rw [he1]; rfl
  have hsymm' : e.symm (topLast (locGrid ch.G t w) (j + 1 + 1)) = Sum.inr () := by
    rw [Equiv.symm_apply_eq]; ext; rw [he2]; rfl
  unfold facAt locA conAt
  rw [dif_pos hj0, dif_pos hj0]
  unfold lastDat
  rw [← hT₁O O₁ hO₁, ← hT₂O O₂ hO₂]
  refine ⟨fun hrel => ?_, fun hexp => ?_⟩
  · have e1 := key S 0 hc' (fun y y' => by
      rw [Submodule.coe_zero, Pi.zero_apply, zero_mul]
      exact (hrel y (y'.submatrix e.symm id)).symm)
    have e2 := key ∅ 0 (fun i hi => absurd hi (Finset.notMem_empty i)) (fun y y' => by
      rw [Submodule.coe_zero, Pi.zero_apply, zero_mul, Finset.sum_empty])
    rw [Finset.sum_empty] at e2
    exact e1.symm.trans e2
  · rw [← hT₁Φ, ← hT₂Φ]
    refine key S Φ₂ hc' fun y y' => ?_
    rw [hΦ₂, hΦ₁]
    refine Eq.trans ?_ (hexp (y, y'.submatrix e.symm id))
    rw [dif_pos (show j + 2 * 0 + 2 = (locGrid ch.G t w).m from hj0)]
    have hy : y'.toRows₁.submatrix (Fin.cast h₃) (Fin.cast h₄) = (y'.submatrix e.symm id).submatrix
        (Fin.castLE (show (locGrid ch.G t w).rank ((locGrid ch.G t w).m, j + 1 + 1) ≤ _ by simp only [hm]; omega))
        (Fin.cast (show (locGrid ch.G t w).rank ((locGrid ch.G t w).m, j + 1) = _ by simp only [hm]; omega)) := by
      funext a b
      simp only [Matrix.submatrix_apply, Matrix.toRows₁_apply, id]
      exact congrArg (fun z => y' z (Fin.cast h₄ b)) (hsymm a).symm
    have hy' : (y'.submatrix e.symm id) (topLast (locGrid ch.G t w) (j + 1 + 1)) = y' (Sum.inr ()) := by
      funext b
      simp only [Matrix.submatrix_apply, id]
      rw [hsymm']
    simp only
    rw [hy, hy']
    rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlacePointConditionTorusInverseDiagIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlace_pointCondition_torus_inverseDiag_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∃ u : UX D ρ, ∃ a ∈ p.A₁, GlobalTheory.AscFin.MxOff (· = v) (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a)) → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.PtInv.inv_int_of_pt | exact GlobalTheory.FinPl.PtInv.inv_int_of_pt | (intros; apply GlobalTheory.FinPl.PtInv.inv_int_of_pt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceShiftConditionTorusDiagIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlace_shiftCondition_torus_diag_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ N : Mx D ρ ρ, MxAt (· = v) N → (∀ i j, j ≤ i → N i j = 0) → mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ N) ∈ p.A₁ → psiE ψ (upSum N) = 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.AscFin.ShiftInt.shift_int | exact GlobalTheory.AscFin.ShiftInt.shift_int | (intros; apply GlobalTheory.AscFin.ShiftInt.shift_int <;> assumption)
end

